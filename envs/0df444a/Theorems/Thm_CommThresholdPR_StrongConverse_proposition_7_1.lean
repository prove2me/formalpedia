-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_proposition_7_1
-- name    : CommThresholdPR.StrongConverse.proposition_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:19.840596+00:00
-- url     : https://prove2.me/theorems/cb00845d-b71d-4f84-9ea8-aa66529a926c
-- title:
--   Proposition 7.1 — all information-budget bounds
-- statement:
--   Suppose an $n$-copy protocol $\Pi_n$ has cost at most $nR$, actual success probability $p>0$, $R\ge0$ and $0<\varepsilon<1$, and $\delta(n,p)\le1/2$. Eligible deterministic tape fixings and selected sets from Construction 4.1 exist. For every such choice, let $\pi$ be its actual Construction 5.1 protocol and $C=\operatorname{IC}_{\mu}(\pi)$. Then
--   $$C\le R+\left(2+\frac{L_{\rm out}}{-\log_2(1-\varepsilon)}\right)\frac{\log_2(1/p)}n+2L_{\rm in}\delta(n,p)+4h(\delta(n,p)).$$
--   Both information-budget cases hold:
--   $$C\le R\ \Longrightarrow\ \operatorname{err}_{\mu}(R)\le\varepsilon+\delta(n,p),$$
--   $$C>R\ \Longrightarrow\ \operatorname{err}_{\mu}(R)\le\varepsilon+\delta(n,p)+2\left(1-\frac RC\right)\sqrt{(\ln2)\left[R+\left(2+\frac{L_{\rm out}}{-\log_2(1-\varepsilon)}\right)\frac{\log_2(1/p)}n\right]}.$$
--   The original protocol is arbitrary and randomized; the deterministic reduction is an existence conclusion and the simulation is computed operationally. The zero-rate case is included.
--
--   Differences from the source:
--   - encoding: finite public randomness and independent finite private random tapes → finite public seeds and private local kernels on finite binary trees; reason: finite contingent choice tables realize the kernels as independent private tapes; posterior local tape laws recover every source transcript/output law and cost without any uniform bound
--   - encoding: Construction 4.1 with [n], X_<J, Y_>J and (T,A_S,B_S) → zero-based Fin n, dependent prefix/suffix carriers and a reversible binary encoding of the augmented transcript; reason: the coordinate reindexing and transcript encoding are bijective; Q and q are computed from the actual deterministic execution
--   - encoding: Construction 5.1 with alternating messages and publicly fixed empty turns → the public augmented binary tree with actual binary encodings of finite auxiliary messages; reason: omitting publicly determined empty turns preserves the public history information; all nonempty messages are transmitted and only (J,X_<J) is public randomness
--   - encoding: operational infima on nonempty sets bounded below by zero → a guarded real infimum over the entire protocol type; reason: on the source domain input exchange and zero-message protocols ensure nonemptiness and finite information is nonnegative; the fallback is only outside that domain, with these facts left to solvers
--   - encoding: fix randomness and choose S before constructing the single-instance protocol → explicit existence of an eligible fixation and set, followed by the bounds for every eligible choice; reason: these are precisely the finite construction witnesses used by the source; no continuity, divergence or information conclusion is a hypothesis
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Proposition 7.1, pp. 22–23, (45)–(47); deterministic reduction §4, p. 12, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem proposition_7_1 {n : ℕ} (hn : 0 < n)
    (g : TotalRelation X Y A B) (μ : PMF (X × Y))
    (piN : Protocol (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
    (R p ε : ℝ) (hR : 0 ≤ R) (hcost : (piN.cost : ℝ) ≤ n * R)
    (hp : p = 1 - protocolError (repeated g n) (inputPower μ n) piN)
    (hp0 : 0 < p) (hε : 0 < ε) (hε1 : ε < 1) (hδ : delta n p ≤ 1 / 2) :
    (∃ e : Extraction X Y A B n,
      e.g = g ∧ e.μ = μ ∧ piN.fixed e.tree ∧ e.Setup R p ε) ∧
    (∀ e : Extraction X Y A B n,
      e.g = g → e.μ = μ → piN.fixed e.tree → e.Setup R p ε →
      (let C := (e.simulation hn).info μ
       C ≤ R + (2 + logOutput A B / (-Real.logb 2 (1 - ε))) *
         Real.logb 2 (1 / p) / n +
           2 * logInput X Y * delta n p + 4 * WildeQIT.binaryEntropy (delta n p) ∧
       (C ≤ R → errorAtRate g μ R ≤ ε + delta n p) ∧
       (R < C → errorAtRate g μ R ≤ ε + delta n p +
         2 * (1 - R / C) * Real.sqrt (Real.log 2 *
           (R + (2 + logOutput A B / (-Real.logb 2 (1 - ε))) *
             Real.logb 2 (1 / p) / n))))) := by sorry

end CommThresholdPR.StrongConverse
