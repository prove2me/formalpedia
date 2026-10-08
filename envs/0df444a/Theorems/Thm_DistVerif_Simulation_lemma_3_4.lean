-- Prove2me | Theorems.Thm_DistVerif_Simulation_lemma_3_4
-- name    : DistVerif.Simulation.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:09.981981+00:00
-- url     : https://prove2.me/theorems/e71ecab3-270c-4c92-8fc2-c2c2150423cf
-- title:
--   Lemma 3.4 — $C_{L_t}$, $C_{R_t}$ are fixed functions of $C_{L_{t-1}}$, $C_{R_{t-1}}$ and $dp$ $B$-bit messages
-- statement:
--   Let $\mathcal A$ be a deterministic B-model algorithm on the network $G(\Gamma,d,p)$ of §3.1, with inputs $x$ at $s=u^p_0$ and $y$ at $r=u^p_{d^p-1}$, and write $C_{L_t}=C_{\mathcal A}(L_t,t,x,y)$ and $C_{R_t}=C_{\mathcal A}(R_t,t,x,y)$ for the configurations of the $t$-left and $t$-right sets at the end of round $t$. Let $0<t<(d^p-1)/2$. Then:
--
--   1. **(3.2)** There are $dp$ slots, each either empty or an edge $(w,u)$ of $G(\Gamma,d,p)$ with $w\in L_{t-1}$, and a function $g_R$, such that for all inputs $x,y$
--   $$C_{R_t}=g_R\big(C_{R_{t-1}},M^{L_{t-1}}_1,\dots,M^{L_{t-1}}_{dp}\big),$$
--   where $M^{L_{t-1}}_i$ is the $B$-bit message sent in round $t$ along the edge of slot $i$ (and a fixed dummy message if slot $i$ is empty).
--   2. **(3.1)** Symmetrically, there are $dp$ slots, each empty or an edge $(w,u)$ with $w\in R_{t-1}$, and a function $g_L$, such that for all inputs $x,y$
--   $$C_{L_t}=g_L\big(C_{L_{t-1}},M^{R_{t-1}}_1,\dots,M^{R_{t-1}}_{dp}\big).$$
--
--   This is the step of the Simulation Theorem: Bob, who knows $C_{R_{t-1}}$, can compute $C_{R_t}$ once Alice sends him $dp$ messages of $B$ bits, which she can compute from $C_{L_{t-1}}$, and vice versa.
--
--   **Formalization Note** The functions $g_L,g_R$ and the slot edges are chosen once, before the inputs, and depend only on $\mathcal A$, $t$ and the network. The paper's wording ("Fix any deterministic algorithm $\mathcal A$ and input strings $x$ and $y$ … there exist functions") read literally would let $g_R$ depend on $(x,y)$, which makes the lemma trivial; its proof constructs input-independent functions and edges, and the proof of Theorem 3.1 needs that, since Bob evaluates $g_R$ without knowing $x$. Empty slots are the paper's padding ("if there are less than $dp$ such messages, then we add some empty messages"). The node indices $s,r$ need $d^p\ge1$, which is a hypothesis.
-- source:
--   Das Sarma, Holzer, Kor, Korman, Nanongkai, Pandurangan, Peleg, Wattenhofer, Distributed Verification and Hardness of Distributed Approximation, SIAM J. Comput. 41 (2012), p. 1249, Lemma 3.4, equations (3.1)–(3.2); proof on pp. 1249–1250

import Mathlib
import Definitions.Def_DistVerif_Simulation_Network
import Definitions.Def_DistVerif_Simulation_Algorithm

namespace DistVerif.Simulation

/-- **Lemma 3.4** (p. 1249). Let `A` be a deterministic B-model algorithm on `G(Γ, d, p)`
(inputs at `s = u^p_0` and `r = u^p_{d^p-1}`) and `0 < t < (d^p - 1)/2`.
* (3.2) There are `d·p` slots `eR`, each either empty or an edge `(w, u)` of the graph with
  `w ∈ L_{t-1}`, and a function `gR`, both independent of the inputs, such that for all inputs
  `x, y` the configuration `C_{R_t}` equals `gR` applied to `C_{R_{t-1}}` and the `B`-bit
  messages sent along the slots' edges in round `t` (an all-`false` message for empty slots).
* (3.1) Symmetrically for `C_{L_t}`, with `d·p` edges leaving `R_{t-1}` and a function `gL`. -/
theorem lemma_3_4 (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b)
    (t : ℕ) (ht0 : 0 < t) (ht : (t : ℝ) < ((d : ℝ) ^ p - 1) / 2) :
    (∃ eL : Fin (d * p) → Option (Vtx Γ d p × Vtx Γ d p),
      ∃ gL : (↥(L Γ d p (t - 1)) → A.State) → (Fin (d * p) → Msg B) → (↥(L Γ d p t) → A.State),
        (∀ i w u, eL i = some (w, u) → w ∈ R Γ d p (t - 1) ∧ (graph Γ d p).Adj w u) ∧
        ∀ x y : Fin b → Bool,
          (fun v : ↥(L Γ d p t) =>
              A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y t v) =
            gL (fun v : ↥(L Γ d p (t - 1)) =>
                  A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y (t - 1) v)
               (fun i => match eL i with
                 | some (w, u) => A.send w u
                     (A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y (t - 1) w)
                 | none => fun _ => false)) ∧
    (∃ eR : Fin (d * p) → Option (Vtx Γ d p × Vtx Γ d p),
      ∃ gR : (↥(R Γ d p (t - 1)) → A.State) → (Fin (d * p) → Msg B) → (↥(R Γ d p t) → A.State),
        (∀ i w u, eR i = some (w, u) → w ∈ L Γ d p (t - 1) ∧ (graph Γ d p).Adj w u) ∧
        ∀ x y : Fin b → Bool,
          (fun v : ↥(R Γ d p t) =>
              A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y t v) =
            gR (fun v : ↥(R Γ d p (t - 1)) =>
                  A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y (t - 1) v)
               (fun i => match eR i with
                 | some (w, u) => A.send w u
                     (A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y (t - 1) w)
                 | none => fun _ => false)) := by sorry

end DistVerif.Simulation
