-- Prove2me | Theorems.Thm_ClusterDecomp_claim_3_8
-- name    : ClusterDecomp.claim_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:38.346338+00:00
-- url     : https://prove2.me/theorems/8b309167-b7c4-4323-9d3a-235cbd5736e8
-- title:
--   Claim 3.8, p.17 — $w(S,P_i\setminus S)/\min\{\mathrm{vol}(S),\mathrm{vol}(P_i\setminus S)\}\ge\varepsilon\rho_G(k+1)/(32\sqrt e\,k)$
-- statement:
--   Under the hypotheses of Theorem 1.1, let $B_i$ be returned by Algorithm 1 on $A_i$ and $P_i$ by Algorithm 2 on the $B_i$. For every positive-volume $S\subsetneq P_i$ with $\mathrm{vol}(S\cap B_i)\le\mathrm{vol}(B_i)/2$,
--   $$\frac{w(S,P_i\setminus S)}{\min\{\mathrm{vol}(S),\mathrm{vol}(P_i\setminus S)\}}\ge\frac{\varepsilon\,\rho_G(k+1)}{32\sqrt e\,k}.$$
--
--   At least one side of every cut of $P_i$ satisfies the hypothesis, so this lower-bounds the inner conductance of $P_i$.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights with positive degrees; reason: the argument uses neither integrality nor the ratio, and integer weights are an instance
--   - encoding: "the backbone returned by Algorithm 1", which computes an α-fair cut → every B = T ∖ {t} of every α-fair s,t-cut of H_A (Alg1Run); reason: the paper fixes nothing about the cut beyond fairness; the relation covers whatever the black box returns
--   - encoding: "the partition returned by Algorithm 2" → every recursion tree with every balanced split and every α_a-fair cut (Alg2Run); reason: the paper fixes nothing beyond balance and fairness; the relation covers every execution
--   - generalization: ρ_G(k+1) in the formula → any real r with r ≤ ρ_G(k+1) and (1+ε)p ≤ r; reason: U, T (resp. S) exist here, so ρ_G(k+1) < ⊤ and r = ρ_G(k+1) is the printed statement
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Claim 3.8, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg1Run
import Definitions.Def_ClusterDecomp_Alg2Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Claim 3.8.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), Claim 3.8, p.17 (PDF p.19).

"For every positive-volume S ⊊ Pi satisfying vol(S ∩ Bi) ≤ vol(Bi)/2, we have
w(S, Pi ∖ S)/min{vol(S), vol(Pi ∖ S)} ≥ ερG(k + 1)/(32√e k)."

Backbones come from Algorithm 1 on the family `A`, then the partition from Algorithm 2.

**Formalization Note.** `r` is any real with `r ≤ ρ_G(k+1)` and `(1+ε)p ≤ r`. Since `S ⊊ P_i` has positive volume and every vertex has positive degree, there are
more than `k` vertices, so `ρ_G(k+1) < ⊤` and `r = ρ_G(k+1)` is the printed statement. The denominator is positive for the same reason. -/
theorem claim_3_8 {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) {k : ℕ} {A : Fin k → Finset V}
    {ε p : ℝ} (hF : Family G k A ε p) {B P : Fin k → Finset V}
    (hB : ∀ i, Alg1Run G (A i) ε p (B i)) (hP : Alg2Run G B P) (i : Fin k) {S : Finset V}
    (hS : S ⊂ P i) (hS0 : 0 < G.vol S) (hSB : G.vol (S ∩ B i) ≤ G.vol (B i) / 2)
    (r : ℝ) (hr : ENNReal.ofReal r ≤ G.rho (k + 1)) (hr' : (1 + ε) * p ≤ r) :
    ε * r / (32 * Real.sqrt (Real.exp 1) * k) ≤
      G.cut S (P i \ S) / min (G.vol S) (G.vol (P i \ S)) := by sorry

end ClusterDecomp
