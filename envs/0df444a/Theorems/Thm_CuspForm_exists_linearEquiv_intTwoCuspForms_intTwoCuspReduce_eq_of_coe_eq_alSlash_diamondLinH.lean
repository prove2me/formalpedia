-- Prove2me | Theorems.Thm_CuspForm_exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH
-- name    : CuspForm.exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/92872351-7546-5c3e-b223-3c59f29d711f
-- title:
--   Atkin–Lehner transport of two-cusp integral weight-two forms mod p
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` in $(\mathbb{Z}/(M/p))^\times$ is $1$, let $W$ be an Atkin–Lehner datum at $(M,p)$, that is, a natural number $R$ with $M = pR$ together with integers $a,b$ satisfying $pa - Rb = 1$, and let $e \in (\mathbb{Z}/M)^\times$. Write $L =$ `twoCuspLattice M H 2 p ⊥` for the span, over the smallest subring of $\mathbb{C}$, of the set of those weight-two cusp forms $f$ on [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) for which, for every $t$ in the Hecke subring `heckeRingH M H 2`, every Atkin–Lehner datum $W'$ at $(M,p)$ and every $n$, the $n$-th $q$-expansion coefficients of $t f$ and of $(t f) \mid_2 W'$ both lie in that subring; and write [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) for the quotient of $L$ by `intIdeal p • ⊤`, with [`CuspForm.intTwoCuspReduce`](def/ModularCurve_XHDifferentialsModL.html#L401) the quotient map. Then there is a $\mathbb{Z}/p$-linear automorphism $\omega_W$ of [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) with the following property: whenever $f$ is a weight-two cusp form on [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) belonging to that integral set, and $g$ is a weight-two cusp form on the same group whose underlying function on the upper half-plane equals [`ModularForm.alSlash W 2`](def/ModularForm_AtkinLehnerDatum.html#L141) applied to the function of $\langle e\rangle f =$ [`CuspForm.diamondLinH 2 e f`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), then $g$ also belongs to the integral set and $\omega_W$ sends the class of $f$ to the class of $g$.
--
--   This records that the Atkin–Lehner transport $f \mapsto (\langle e\rangle f)\mid_2 W$ preserves the lattice of two-cusp integral weight-two forms on $\Gamma_H(M)$ and induces an automorphism of its reduction modulo $p$, the automorphism being characterised by its values on classes of integral forms against any cusp form representing the transported function. It is used in the comparison of this mod $p$ space with the differentials on the modular curve, via [`CuspForm.exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet`](thm.html#CuspForm.exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ) :
    ∃ ωW : CuspForm.IntTwoCuspForms M H p ≃ₗ[ZMod p] CuspForm.IntTwoCuspForms M H p,
      ∀ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
        (g : CuspForm (CohCarrier.GammaH M H) 2), ⇑g = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f) →
        ∃ hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ),
          ωW (CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) = CuspForm.intTwoCuspReduce M H p ⟨g, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hg⟩ := by sorry
