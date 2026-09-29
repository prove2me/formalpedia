-- Prove2me | Theorems.Thm_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral
-- name    : CuspForm.exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/56cf520c-113f-51a0-b400-237013c096ed
-- title:
--   Serre's Eisenstein-trace congruence at level Γ_H(M)
-- statement:
--   Fix a prime $p$ and $M\neq 0$, together with an Atkin–Lehner datum $W$ for $(M,p)$: an integer $R=W.R$ with $M=pR$ and integers $a_W,b_W$ satisfying $pa_W-Rb_W=1$, giving the matrix $W.\mathrm{alGL}\in GL_2(\mathbb R)$ and the operator $\mathrm{alSlash}\,W\,k\,f=f\mid_k W$. Let $H\le(\mathbb Z/M)^\times$ contain every unit whose reduction modulo $R$ is $1$, and let $d\in(\mathbb Z/M)^\times$ have reduction inverse to $p$ in $\mathbb Z/R$. Let $a\in\mathbb N$ with $a\ge 3$, $a$ even and $(p-1)\mid a$; let $\mathfrak m$ be a prime ideal of the ring $\overline{\mathbb Z}$ of algebraic integers in $\mathbb C$ containing $p$. Let $w\ge 2$ and let $F$ be a cusp form of weight $w$ for $\Gamma_H(M)$, the image in $SL_2(\mathbb Z)$ of the matrices of $\Gamma_0(M)$ whose lower-right entry reduces into $H$. Assume every $q$-expansion coefficient $\mathrm{qCoeff}\,F\,n$ is $\mathfrak m$-integral, i.e. of the form $x/y$ with $x,y\in\overline{\mathbb Z}$, $y\notin\mathfrak m$, and assume there is $c\in\mathbb N$ such that $p^{c}$ times each coefficient of $(\langle d\rangle F)\mid_w W$ is likewise $\mathfrak m$-integral, where $\langle d\rangle$ is [`CuspForm.diamondLinH`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132). Then there is $i_0$ such that for every $i\ge i_0$ there is a cusp form $G$ of weight $w+ia$ for $\Gamma_{H'}(R)$, $H'$ the image of $H$ in $(\mathbb Z/R)^\times$, all of whose $q$-coefficients are $\mathfrak m$-integral and which satisfies, for all $n$, the congruence $xy'-x'y\in\mathfrak m$ whenever $x=y\,\mathrm{qCoeff}\,F\,n$ and $x'=y'\,\mathrm{qCoeff}\,G\,n$ with $y,y'\notin\mathfrak m$; that is, $a_n(G)\equiv a_n(F)\pmod{\mathfrak m}$ for all $n$.
--
--   This is Serre's Eisenstein-trace form of level lowering modulo $\mathfrak m$, transposed from $\Gamma_0$ to level $\Gamma_H(M)$, with the Eisenstein weight $a$ and the multiplicity $i$ left explicit so that two forms may be raised to a common weight. It is used to prove the inclusion of mod-$p$ $q$-expansion function fields [`ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup`](thm.html#ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularFormClass
open scoped MatrixGroups ModularForm

theorem CuspForm.exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral
    (p : ℕ) [Fact p.Prime] {M : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ) (hd : (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d : ZMod W.R) * (p : ZMod W.R) = 1)
    (a : ℕ) (ha : 3 ≤ a) (ha2 : Even a) (hpa : p - 1 ∣ a)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (w : ℤ) (hw : 2 ≤ w) (F : CuspForm (CohCarrier.GammaH M H) w)
    (hFint : ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff F n)
    (hFW : ∃ c : ℕ, ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧
      (x : ℂ) = y * (p : ℂ) ^ c * qCoeff (ModularForm.alSlash W w ⇑(CuspForm.diamondLinH w d F)) n) :
    ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
      ∃ G : CuspForm (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm)))) (w + i * a),
        (∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff G n) ∧
        (∀ (n : ℕ) (x y x' y' : integralClosure ℤ ℂ), y ∉ 𝔪 → y' ∉ 𝔪 →
          (x : ℂ) = y * qCoeff F n → (x' : ℂ) = y' * qCoeff G n → x * y' - x' * y ∈ 𝔪) := by sorry
