-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_2_3
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:34.3079+00:00
-- url     : https://prove2.me/theorems/733cb5b5-7294-4899-8805-b1e0a18456b2
-- title:
--   Lemma 2.3 — bipartite 2-expansion with isolated left vertices
-- statement:
--   For every finite bipartite graph with parts $L,R$, one deterministic polynomial-time program finds $Q\subseteq L$, $Z\subseteq R$ and witness edges $M\subseteq Q\times Z$ satisfying
--
--   $$
--   N(Q)=Z,\qquad |L\setminus Q|\le2|R\setminus Z|.
--   $$
--
--   Each vertex of $Z$ has exactly two incident witness edges, and each vertex of $Q$ has at most one. The sets may be empty; every isolated vertex of $L$ belongs to $Q$. The program outputs all three sets as finite indicators.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - reading: polynomial-time algorithm without a named machine → one finite charged register program, with fair random bits in rational bit-cost executions and exact-real arithmetic/Bernoulli(p) access for real inputs; reason: this makes the implicit computational model explicit without admitting optimization instructions or semantic callbacks
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 2.3, printed p.17 (PDF p.18), proof continuing printed p.18 (PDF p.19)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Preclustering
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Encoding

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_2_3 :
  ∃ code : Program, Deterministic code ∧ ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
    ∀ l r (E : Fin l → Fin r → Prop),
      let oracle : ℕ → ℕ → ℕ → ℝ := fun bank u v =>
        if h : bank = 0 ∧ u < l ∧ v < r then (if E ⟨u,h.2.1⟩ ⟨v,h.2.2⟩ then 1 else 0) else 0
      let initial : MachineState :=
        {initialState l with natReg := Function.update (initialState l).natReg 1 r, work := l+r+1}
      let B := polynomialBound C d (l+r)
      BoundedRun true code oracle initial B ∧
      ∀ st ∈ (machineRun true code oracle initial B).support,
        let Q := (Finset.univ : Finset (Fin l)).filter (fun u => st.natMem u.val = 1)
        let Z := (Finset.univ : Finset (Fin r)).filter (fun v => st.natMem (l+v.val) = 1)
        let M := (Finset.univ : Finset (Fin l × Fin r)).filter
          (fun e => st.natMem (l+r+e.1.val*r+e.2.val) = 1)
        ExpansionCertificate E Finset.univ Finset.univ Q Z M := by sorry

end ConstrainedCorrelationRepulsion.Main
