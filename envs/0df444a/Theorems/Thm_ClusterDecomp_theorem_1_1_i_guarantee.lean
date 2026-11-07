-- Prove2me | Theorems.Thm_ClusterDecomp_theorem_1_1_i_guarantee
-- name    : ClusterDecomp.theorem_1_1_i_guarantee
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:51.562018+00:00
-- url     : https://prove2.me/theorems/7838ded6-09a0-4965-b922-6b9b0f84fe6e
-- title:
--   Proof of Theorem 1.1(i), p.14 — the backbones have the outer and inner conductance guarantees
-- statement:
--   Under the hypotheses of Theorem 1.1, let $B_i$ be returned by Algorithm 1 on $A_i$, for each $i$. Then the $B_i$ are pairwise disjoint, and for every $i$: $B_i\subseteq A_i$, $\mathrm{vol}(B_i)>0$, and
--   $$\phi_G(B_i)\le\Bigl(1+\frac\varepsilon{16}\Bigr)p,\qquad \phi(G\{B_i\})\ge\frac{\varepsilon\,\rho_G(k+1)}9.$$
--
--   This is the combinatorial content of Theorem 1.1(i), with no machine.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights with positive degrees; reason: the argument uses neither integrality nor the ratio, and integer weights are an instance
--   - encoding: "the backbone returned by Algorithm 1", which computes an α-fair cut → every B = T ∖ {t} of every α-fair s,t-cut of H_A (Alg1Run); reason: the paper fixes nothing about the cut beyond fairness; the relation covers whatever the black box returns
--   - encoding: ϕ(G{B_i}), ρ_G(k+1) as real minima → values in ℝ≥0∞ with ⊤ on an empty family (a singleton S; k equal to the number of vertices); reason: the printed minima are undefined there; ε > 0 gives ε·⊤ = ⊤, and .toReal is never applied, so the bound stays meaningful
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), proof of Theorem 1.1(i), p.14 (PDF p.16)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg1Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Proof of Theorem 1.1(i): the guarantees.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), proof of Theorem 1.1(i), p.14 (PDF p.16).

"By Lemma 3.2, every Bi has positive volume and satisfies ϕG(Bi) ≤ αp = (1 + ε/16) p. Thus, it remains to bound ϕ(G{Bi}). […] Since this
holds for every U ⊆ Bi with 0 < vol(U) ≤ vol(Bi)/2, we conclude that ϕ(G{Bi}) ≥ ερG(k + 1)/9."

For the family `A` and any outputs `B i` of Algorithm 1 on `A i`, with the machine left out.

**Formalization Note.** The inner bound is in `ℝ≥0∞`; `ε > 0`, so `ε · ⊤ / 9 = ⊤`. This occurs only when `k` is the number of vertices, and then each
`B i` is a singleton and `ϕ(G{B i}) = ⊤`. -/
theorem theorem_1_1_i_guarantee {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) {k : ℕ}
    {A : Fin k → Finset V} {ε p : ℝ} (hF : Family G k A ε p) {B : Fin k → Finset V}
    (hB : ∀ i, Alg1Run G (A i) ε p (B i)) :
    (Pairwise fun a b => Disjoint (B a) (B b)) ∧
      ∀ i, B i ⊆ A i ∧ 0 < G.vol (B i) ∧ G.phiOut (B i) ≤ (1 + ε / 16) * p ∧
        ENNReal.ofReal (ε / 9) * G.rho (k + 1) ≤ (G.degPres (B i)).phi := by sorry

end ClusterDecomp
