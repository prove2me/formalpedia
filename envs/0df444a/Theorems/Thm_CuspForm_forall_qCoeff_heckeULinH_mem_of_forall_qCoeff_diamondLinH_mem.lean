-- Prove2me | Theorems.Thm_CuspForm_forall_qCoeff_heckeULinH_mem_of_forall_qCoeff_diamondLinH_mem
-- name    : CuspForm.forall_qCoeff_heckeULinH_mem_of_forall_qCoeff_diamondLinH_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/44cb80ab-bdd5-55ef-a941-e60646fc650f
-- title:
--   U_q preserves two-cusp A-integrality, given the diamonds
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial. Let $A$ be a subring of $\mathbb{C}$. Call a weight-two cusp form $g$ for the group [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) (the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the lower-right-entry character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$) two-cusp $A$-integral if, for every Atkin–Lehner datum $W$ for $(M,p)$ — that is, data $R$, $a$, $b$ with $M = pR$ and $pa - Rb = 1$ — all coefficients $a_n(g)$ of the width-one $q$-expansion of $g$ and all coefficients $a_n(g \mid_2 W)$ of the slash of $g$ by the associated matrix in $\mathrm{GL}_2(\mathbb{R})$ lie in $A$. Assume (hypothesis `hdia`) that each diamond operator [`CuspForm.diamondLinH 2 d`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132), $d \in (\mathbb{Z}/M)^\times$, carries two-cusp $A$-integral forms to two-cusp $A$-integral forms. Then for every prime $q$ dividing $M$ and every two-cusp $A$-integral $f$, the form [`CuspForm.heckeULinH 2 q f`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171), i.e. $U_q f$, is again two-cusp $A$-integral.
--
--   This is the $U_q$ step ($q \mid M$) in the verification that the naive two-cusp $A$-integrality condition — integrality of the $q$-expansions both at $\infty$ and after slashing by an Atkin–Lehner matrix at $p$ — defines a Hecke-stable $A$-submodule of weight-two cusp forms on $\Gamma_H(M)$, the diamond case being assumed as a hypothesis. It is used in [`CuspForm.mem_twoCuspIntegralSet_ratLocalizedAt_of_forall_qCoeff_mem`](thm.html#CuspForm.mem_twoCuspIntegralSet_ratLocalizedAt_of_forall_qCoeff_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_forall_qCoeff_heckeULinH_mem_of_forall_qCoeff_diamondLinH_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.forall_qCoeff_heckeULinH_mem_of_forall_qCoeff_diamondLinH_mem
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
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(f)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(f)) n ∈ A) :
    ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(CuspForm.heckeULinH 2 q f)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.heckeULinH 2 q f)) n ∈ A := by sorry
