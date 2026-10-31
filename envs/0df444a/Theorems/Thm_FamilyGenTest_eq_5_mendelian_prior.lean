-- Prove2me | Theorems.Thm_FamilyGenTest_eq_5_mendelian_prior
-- name    : FamilyGenTest.eq_5_mendelian_prior
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:12:46.566586+00:00
-- url     : https://prove2.me/theorems/ed0764a2-3aad-4a77-a5b7-b890ffc0b5ec
-- title:
--   Eq. (5) with Table 1 — the Mendelian product is a prior
-- statement:
--   Let $\mathcal I$ be a finite family with a pedigree, and let $p_i(\gamma)=\mathbb P(G_i=\gamma)$, $i\in\mathcal F$, be founder priors: nonnegative, with $\sum_{\gamma}p_i(\gamma)=1$. Then the Mendelian product (5) is nonnegative and
--   $$
--   \sum_{g\in\{0,1,2\}^{\mathcal I}}\ \prod_{i\in\mathcal F}p_i(g_i)\prod_{i\in\mathcal I\setminus\mathcal F}\mathbb P(G_i=g_i\mid g_{\mathrm{fa}(i)},g_{\mathrm{mo}(i)})=1.
--   $$
--
--   This ties the mission's arbitrary prior to the paper's Bayesian network: (5) is one of the priors that the goal covers.
--
--   Differences from the source:
--   - reading: a set of genes $\mathcal J$ in the model of §2; Assumption 4, Assumption 5 and Theorem 1's proof are single-gene → one gene: $g_i\in\{0,1,2\}$; reason: Theorem 1 compares $\mathbb P_i(\mathbf s)$ with two real thresholds, which needs a scalar; its proof, Assumption 4 and §4.3 are single-gene (pp.15, ec2), and no multi-gene threshold statement is printed
--   - encoding: (5) as a product over founders times a product over nonfounders → one product over $\mathcal I$ with a case on `parents i`, and a `rank` function for acyclicity; reason: same product; the rank says that the Bayesian network is acyclic
--   - generalization: a pedigree in which every nonfounder has a father and a mother → `Pedigree`: `parents i = some (f, m)` with an acyclic rank, $f\ne m$ not required; reason: every pedigree of the paper is one, and the product (5) is still a mass function
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), (5), p.11; Table 1, p.12

import Mathlib
import Definitions.Def_FamilyGenTest_Pedigree

namespace FamilyGenTest

/-- Eq. (5) with Table 1 (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694
(Jan 24 2023), pp.11–12): given founder priors that are mass functions, the Mendelian product is
nonnegative and sums to `1`, so it is a `Prior`. -/
theorem eq_5_mendelian_prior {I : Type*} [Fintype I] [DecidableEq I] (P : Pedigree I)
    (p : I → Fin 3 → ℝ) (hp0 : ∀ i, P.parents i = none → ∀ γ, 0 ≤ p i γ)
    (hp1 : ∀ i, P.parents i = none → ∑ γ, p i γ = 1) :
    (∀ g, 0 ≤ mendelian P p g) ∧ ∑ g, mendelian P p g = 1 := by sorry

end FamilyGenTest
