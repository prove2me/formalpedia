-- Prove2me | Theorems.Thm_CuspForm_exists_weight_ge_qCoeff_congr_level_div_of_alSlash_p_integral
-- name    : CuspForm.exists_weight_ge_qCoeff_congr_level_div_of_alSlash_p_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/1e8c526b-8ad5-56ce-b3d1-4a62c4b942e3
-- title:
--   Congruence of a level-pN' cusp form to higher weight level N'
-- statement:
--   Let $p$ be an odd prime and $N'\ge 1$, and let $A$ be an Atkin–Lehner datum for the level $pN'$ at $p$, that is, a cofactor $R$ together with a proof that $pN'=pR$ (so $R=N'$) and integers $a,b$ with $pa-Rb=1$. Let $\mathfrak m$ be a prime ideal of the ring $\overline{\mathbb Z}$ of algebraic integers in $\mathbb C$ containing $p$, let $w\ge 2$ be an integer and let $F$ be a cusp form of weight $w$ on $\Gamma_0(pN')$. Write $a_n(h)$ for the $n$-th coefficient of the width-$1$ $q$-expansion of a function on $\mathbb H$. Assume: every $a_n(F)$ is $\mathfrak m$-integral, i.e. there are $x,y\in\overline{\mathbb Z}$ with $y\notin\mathfrak m$ and $x=y\,a_n(F)$; and there is $c\in\mathbb N$ such that for every $n$ there are $x,y\in\overline{\mathbb Z}$ with $y\notin\mathfrak m$ and $x=y\,p^{c}\,a_n(F\mid_w A)$, where $F\mid_w A$ denotes the weight-$w$ slash of $F$ by the invertible real matrix `alGL` attached to $A$. Then there are an integer $k$ and a cusp form $G$ of weight $k$ on $\Gamma_0(N')$ with $w\le k$, $(p-1)\mid k-w$, all $a_n(G)$ $\mathfrak m$-integral in the same sense, and such that for all $n$ and all $x,y,x',y'\in\overline{\mathbb Z}$ with $y,y'\notin\mathfrak m$, $x=y\,a_n(F)$ and $x'=y'\,a_n(G)$, one has $xy'-x'y\in\mathfrak m$; that is, $G\equiv F$ coefficientwise modulo $\mathfrak m$.
--
--   This is Serre's Eisenstein-trace step in the proof of level lowering at $p$ (as in Ribet's report): a cusp form of level $pN'$ whose Atkin–Lehner transform has coefficients of bounded $p$-denominator is congruent modulo $\mathfrak m$ to a form of level $N'$, at the cost of raising the weight within its class modulo $p-1$. It is used in the passage from a newform of level divisible by $p^2$ to data over the Hecke algebra at level prime to $p$, namely by [`WeierstrassCurve.exists_ideal_heckeAlgebra_ordCompl_of_isNewform_sq_dvd`](thm.html#WeierstrassCurve.exists_ideal_heckeAlgebra_ordCompl_of_isNewform_sq_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_weight_ge_qCoeff_congr_level_div_of_alSlash_p_integral.lean

import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularFormClass

theorem CuspForm.exists_weight_ge_qCoeff_congr_level_div_of_alSlash_p_integral (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N' : ℕ) [NeZero N']
    (A : ModularForm.AtkinLehnerDatum (p * N') p)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (w : ℤ) (hw : 2 ≤ w) (F : CuspForm (CongruenceSubgroup.Gamma0 (p * N')) w)
    (hFint : ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff F n)
    (hFW : ∃ c : ℕ, ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧
      (x : ℂ) = y * (p : ℂ) ^ c * qCoeff (ModularForm.alSlash A w ⇑F) n) :
    ∃ (k : ℤ) (G : CuspForm (CongruenceSubgroup.Gamma0 N') k),
      w ≤ k ∧ ((p : ℤ) - 1 ∣ k - w) ∧
      (∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff G n) ∧
      (∀ (n : ℕ) (x y x' y' : integralClosure ℤ ℂ), y ∉ 𝔪 → y' ∉ 𝔪 →
        (x : ℂ) = y * qCoeff F n → (x' : ℂ) = y' * qCoeff G n → x * y' - x' * y ∈ 𝔪) := by sorry
