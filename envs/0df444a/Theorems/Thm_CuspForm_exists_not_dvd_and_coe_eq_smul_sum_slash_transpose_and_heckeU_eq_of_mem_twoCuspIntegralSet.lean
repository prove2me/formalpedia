-- Prove2me | Theorems.Thm_CuspForm_exists_not_dvd_and_coe_eq_smul_sum_slash_transpose_and_heckeU_eq_of_mem_twoCuspIntegralSet
-- name    : CuspForm.exists_not_dvd_and_coe_eq_smul_sum_slash_transpose_and_heckeU_eq_of_mem_twoCuspIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/af062904-50bb-5be5-bad2-1ccdc4c0da7e
-- title:
--   Transposed U_q and Atkin–Lehner pins on two-cusp integral forms
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and $H \le (\mathbb{Z}/M)^\times$ a subgroup containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial. Let $q$ be a prime with $q \mid M$ and $q \neq p$. Let $f$ be a weight-two cusp form for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of the matrices in $\Gamma_0(M)$ whose lower-right entry reduces into $H$, and assume $f$ lies in [`CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)`](def/CuspForm_TwoCuspLattice.html#L54): for every element $t$ of the Hecke subring `heckeRingH M H 2` and every Atkin–Lehner datum $W$ for $(M,p)$, all $q$-expansion coefficients of $t f$ and of $(t f) \mid_2 W$ lie in the subring $\bot$ of $\mathbb{C}$, i.e. are rational integers. Let $Wd$ be an Atkin–Lehner datum for $(M, M/p)$, that is, a factorisation $M = (M/p) \cdot R$ together with $a, b \in \mathbb{Z}$ satisfying $(M/p)a - Rb = 1$, and let $e \in (\mathbb{Z}/M)^\times$. Then there are a natural number $D$ with $p \nmid D$ and a weight-two cusp form $g$ for the same group, again lying in the two-cusp integral set over $\bot$, such that two things hold. First, as functions on the upper half plane,
--   $$g = D \cdot \sum_{j < q} f \mid_2 \left( \begin{pmatrix} q & 0 \\ 0 & 1 \end{pmatrix} \begin{pmatrix} 1 & 0 \\ Mj & 1 \end{pmatrix} \right),$$
--   the second factor being the transpose of $T^{Mj}$, so that the slashing matrices are $\begin{pmatrix} q & 0 \\ Mj & 1 \end{pmatrix}$. Second, for all natural numbers $D_0, D_1$ and all power series $\mathrm{pf}_0, \mathrm{pf}_1$ over the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ whose images in $\mathbb{C}\llbracket X \rrbracket$ are the width-one $q$-expansions of $D_0 \cdot (\langle e \rangle f) \mid_2 Wd$ and of $D_1 \cdot (\langle e \rangle g) \mid_2 Wd$ respectively, where $\langle e \rangle$ denotes [`CuspForm.diamondLinH 2 e`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), one has
--   $$(D D_1) \cdot U_q(\mathrm{pf}_0) = D_0 \cdot \mathrm{pf}_1$$
--   in power series over the integral closure, $U_q$ being the formal operator sending a series to the one whose $n$-th coefficient is its $(qn)$-th coefficient.
--
--   This is the forms-side statement of the compatibility $(U_q^{t} f) \mid W_{M/p} = U_q (f \mid W_{M/p})$ for weight-two forms on $\Gamma_H(M)$, recorded together with integrality: the transposed $U_q$-image of a two-cusp integral form becomes integral after multiplication by a denominator prime to $p$, and the resulting identity is read off on integral power-series representatives of the Atkin–Lehner twists of the diamond translates. It is used in the construction of the $U_q$-transport for reduction maps at infinite level, in [`ModularCurve.IsInfReductionMap.exists_smul_correspondence_heckeAlphaModLH_heckeBetaModLH_apply_eq_of_ne`](thm.html#ModularCurve.IsInfReductionMap.exists_smul_correspondence_heckeAlphaModLH_heckeBetaModLH_apply_eq_of_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_not_dvd_and_coe_eq_smul_sum_slash_transpose_and_heckeU_eq_of_mem_twoCuspIntegralSet.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_PowerSeries_FormalHeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_not_dvd_and_coe_eq_smul_sum_slash_transpose_and_heckeU_eq_of_mem_twoCuspIntegralSet
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) :
    ∃ (D : ℕ) (_ : ¬ p ∣ D) (g : CuspForm (CohCarrier.GammaH M H) 2)
      (_ : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)),
      (⇑g = (D : ℂ) • ∑ j ∈ Finset.range q,
          (⇑f) ∣[(2 : ℤ)] (ModularForm.heckeDiagMatrix q *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) ∧
      (∀ (D₀ : ℕ) (pfW₀ : PowerSeries ↥(integralClosure ℤ ℂ)),
        pfW₀.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
          UpperHalfPlane.qExpansion 1 ((D₀ : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
        ∀ (D₁ : ℕ) (pfW₁ : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW₁.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D₁ : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e g)) →
          ((D * D₁ : ℕ) : ↥(integralClosure ℤ ℂ)) • PowerSeries.heckeU q pfW₀ =
            ((D₀ : ℕ) : ↥(integralClosure ℤ ℂ)) • pfW₁) := by sorry
