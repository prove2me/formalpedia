-- Prove2me | Theorems.Thm_CuspForm_forall_qCoeff_heckeTLinH_mem_of_forall_qCoeff_diamondLinH_mem
-- name    : CuspForm.forall_qCoeff_heckeTLinH_mem_of_forall_qCoeff_diamondLinH_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/c179a446-c22f-533d-93f9-d4ee5a21018f
-- title:
--   Hecke operators T_ℓ preserve two-cusp A-integrality
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ such that every unit of $\mathbb{Z}/M$ whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial lies in $H$, and a subring $A \subseteq \mathbb{C}$. Work with weight-two cusp forms for the group [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of the subgroup of $\Gamma_0(M)$ whose lower-right entry reduces into $H$. Call such a form $g$ two-cusp $A$-integral if for every Atkin–Lehner datum $W$ for $(M,p)$ — an integer $R$ with $M = pR$ together with integers $a,b$ satisfying $pa - Rb = 1$ — and every $n \in \mathbb{N}$, the $n$-th coefficient of the width-one $q$-expansion of $g$ and that of $g \mid_2 W$ (the weight-two slash by the matrix attached to $W$) both lie in $A$. Assume that for every $d \in (\mathbb{Z}/M)^\times$ the diamond operator [`CuspForm.diamondLinH 2 d`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132) sends two-cusp $A$-integral forms to two-cusp $A$-integral forms. Then for every prime $\ell \nmid M$ and every two-cusp $A$-integral $f$, the form [`CuspForm.heckeTLinH 2 hℓ hℓM f`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) is again two-cusp $A$-integral.
--
--   This is the statement that naive integrality of Fourier coefficients at the two cusps $\infty$ and $W\infty$, measured in an arbitrary subring of $\mathbb{C}$, is stable under the Hecke operators $T_\ell$ at primes $\ell$ away from the level, the diamond operators being taken as the only ring-dependent input. It feeds the construction of the two-cusp integral lattice used later, via [`CuspForm.mem_twoCuspIntegralSet_ratLocalizedAt_of_forall_qCoeff_mem`](thm.html#CuspForm.mem_twoCuspIntegralSet_ratLocalizedAt_of_forall_qCoeff_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_forall_qCoeff_heckeTLinH_mem_of_forall_qCoeff_diamondLinH_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.forall_qCoeff_heckeTLinH_mem_of_forall_qCoeff_diamondLinH_mem
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : Subring ℂ)
    (hdia : ∀ (d : (ZMod M)ˣ) (g : CuspForm (CohCarrier.GammaH M H) 2),
      (∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(g)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(g)) n ∈ A) →
      ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d g)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 d g)) n ∈ A)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(f)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(f)) n ∈ A) :
    ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(CuspForm.heckeTLinH 2 hℓ hℓM f)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.heckeTLinH 2 hℓ hℓM f)) n ∈ A := by sorry
