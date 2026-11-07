-- Prove2me | Theorems.Thm_ClusterDecomp_theorem_1_1_ii_guarantee
-- name    : ClusterDecomp.theorem_1_1_ii_guarantee
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:49.993204+00:00
-- url     : https://prove2.me/theorems/a48ec295-e8f2-42ae-be6d-aa55edfe90d6
-- title:
--   Proof of Theorem 1.1(ii), p.18 — the partition has the outer and inner conductance guarantees
-- statement:
--   Under the hypotheses of Theorem 1.1, let $B_i$ be returned by Algorithm 1 on $A_i$ and $P_i$ by Algorithm 2 on the $B_i$. For every $i$, $\mathrm{vol}(P_i)\ge\mathrm{vol}(B_i)$,
--   $$\phi_G(P_i)\le2\sqrt e\,k\,\phi_G(B_i)\le2\sqrt e\,k\Bigl(1+\frac\varepsilon{16}\Bigr)p\le\frac{17\sqrt e}8kp<4kp,$$
--   and
--   $$\phi(G\{P_i\})\ge\frac{\varepsilon\,\rho_G(k+1)}{32\sqrt e\,k}>\frac{\varepsilon\,\rho_G(k+1)}{53k}.$$
--
--   This is the combinatorial content of Theorem 1.1(ii), with no machine.
--
--   **Formalization Note** The last strict inequality fails when $\rho_G(k+1)=+\infty$, so it is stated as the numeric inequality $\frac1{53k}<\frac1{32\sqrt e\,k}$, and then the resulting bound with $53k$ is stated too.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights with positive degrees; reason: the argument uses neither integrality nor the ratio, and integer weights are an instance
--   - encoding: "the backbone returned by Algorithm 1", which computes an α-fair cut → every B = T ∖ {t} of every α-fair s,t-cut of H_A (Alg1Run); reason: the paper fixes nothing about the cut beyond fairness; the relation covers whatever the black box returns
--   - encoding: "the partition returned by Algorithm 2" → every recursion tree with every balanced split and every α_a-fair cut (Alg2Run); reason: the paper fixes nothing beyond balance and fairness; the relation covers every execution
--   - encoding: ϕ(G{B_i}), ρ_G(k+1) as real minima → values in ℝ≥0∞ with ⊤ on an empty family (a singleton S; k equal to the number of vertices); reason: the printed minima are undefined there; ε > 0 gives ε·⊤ = ⊤, and .toReal is never applied, so the bound stays meaningful
--   - encoding: ερ_G(k+1)/(32√e k) > ερ_G(k+1)/(53k) → 1/(53k) < 1/(32√e k) and the bound ϕ(G{P_i}) ≥ ερ_G(k+1)/(53k), both as clauses; reason: ⊤ > ⊤ is false in ℝ≥0∞ at k equal to the number of vertices; the strict link holds on the finite range, which the numeric clause gives
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), proof of Theorem 1.1(ii), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg1Run
import Definitions.Def_ClusterDecomp_Alg2Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Proof of Theorem 1.1(ii): the guarantees.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), proof of Theorem 1.1(ii), p.18 (PDF p.20).

"Since vol(Pi) ≥ vol(Bi), Lemma 3.2 implies ϕG(Pi) ≤ 2√e k ϕG(Bi) ≤ 2√e k (1 + ε/16) p ≤ (17√e/8) kp < 4kp. It remains to bound ϕ(G{Pi}). For every nontrivial cut of
Pi, at least one of its two sides S satisfies vol(S ∩ Bi) ≤ vol(Bi)/2. We apply Claim 3.8 to the side with volume at most vol(Bi)/2, and obtain
ϕ(G{Pi}) ≥ ερG(k + 1)/(32√e k) > ερG(k + 1)/(53k)."

Each link is a clause, for any outputs of Algorithms 1 and 2, with the machine left out.

**Formalization Note.** The last strict link is false at `ρ = ⊤`, so it is stated as the numeric `1/(53k) < 1/(32√e k)`, and then the resulting bound with `53k`. -/
theorem theorem_1_1_ii_guarantee {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) {k : ℕ}
    {A : Fin k → Finset V} {ε p : ℝ} (hF : Family G k A ε p) {B P : Fin k → Finset V}
    (hB : ∀ i, Alg1Run G (A i) ε p (B i)) (hP : Alg2Run G B P) (i : Fin k) :
    G.vol (B i) ≤ G.vol (P i) ∧
      G.phiOut (P i) ≤ 2 * Real.sqrt (Real.exp 1) * k * G.phiOut (B i) ∧
      2 * Real.sqrt (Real.exp 1) * k * G.phiOut (B i) ≤
        2 * Real.sqrt (Real.exp 1) * k * ((1 + ε / 16) * p) ∧
      2 * Real.sqrt (Real.exp 1) * k * ((1 + ε / 16) * p) ≤
        17 * Real.sqrt (Real.exp 1) / 8 * k * p ∧
      17 * Real.sqrt (Real.exp 1) / 8 * k * p < 4 * k * p ∧
      ENNReal.ofReal (ε / (32 * Real.sqrt (Real.exp 1) * k)) * G.rho (k + 1) ≤
        (G.degPres (P i)).phi ∧
      1 / (53 * (k : ℝ)) < 1 / (32 * Real.sqrt (Real.exp 1) * k) ∧
      ENNReal.ofReal (ε / (53 * k)) * G.rho (k + 1) ≤ (G.degPres (P i)).phi := by sorry

end ClusterDecomp
