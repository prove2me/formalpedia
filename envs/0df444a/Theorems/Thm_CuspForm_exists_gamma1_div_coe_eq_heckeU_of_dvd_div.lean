-- Prove2me | Theorems.Thm_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div
-- name    : CuspForm.exists_gamma1_div_coe_eq_heckeU_of_dvd_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/722a5d9f-491f-54a0-a28d-89d2283a3b54
-- title:
--   U_ℓ lowers the level when ℓ² ∣ N
-- statement:
--   Let $N \geq 1$ and let $k \in \mathbb{Z}$. Let $\ell$ be a natural number dividing $N$ and such that $\ell$ also divides $N/\ell$. Let $\varepsilon'$ be a Dirichlet character modulo $N/\ell$ with values in $\mathbb{C}$, and let $f$ be a cusp form of weight $k$ on $\Gamma_1(N)$ whose nebentypus is the character of modulus $N$ obtained from $\varepsilon'$ by change of level along $N/\ell \mid N$: that is, for every $\gamma \in \Gamma_0(N)$ and every $\tau \in \mathbb{H}$ one has $f(\gamma \cdot \tau) = \varepsilon'(\gamma_{11} \bmod N/\ell)\,(\gamma_{10}\tau + \gamma_{11})^{k} f(\tau)$. The assertion is that there exists a cusp form $h$ of weight $k$ on $\Gamma_1(N/\ell)$ with three properties: its underlying function $\mathbb{H} \to \mathbb{C}$ is $\sum_{j=0}^{\ell-1} f \mid_k \begin{pmatrix} 1 & j \\ 0 & \ell\end{pmatrix}$, the weight-$k$ slash sum defining [`ModularForm.heckeU`](def/ModularForm_HeckeOperator.html#L93); the coefficients of its $q$-expansion of period $1$ satisfy $a_n(h) = a_{\ell n}(f)$ for every $n \in \mathbb{N}$; and it has nebentypus $\varepsilon'$, i.e. $h(\gamma \cdot \tau) = \varepsilon'(\gamma_{11})\,(\gamma_{10}\tau + \gamma_{11})^{k} h(\tau)$ for all $\gamma \in \Gamma_0(N/\ell)$ and $\tau \in \mathbb{H}$.
--
--   This is the level-lowering property of the operator $U_\ell$ in the theory of newforms (as in Li's lemma, going back to Atkin–Lehner): when $\ell^2 \mid N$ and the nebentypus already has modulus $N/\ell$, the operator $U_\ell$ carries $S_k(N,\varepsilon)$ into $S_k(N/\ell,\varepsilon')$. It is used in the analysis of primitive forms, in particular for the vanishing of the coefficients $a_{\ell n}$ of a primitive form at such $\ell$ and for the resulting bounds on its $q$-coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_gamma1_div_coe_eq_heckeU_of_dvd_div
    {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ)
    (ε' : DirichletCharacter ℂ (N / ℓ)) (f : CuspForm (Gamma1 N) k)
    (hf : CuspForm.HasNebentypus
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓN) ε') f) :
    ∃ h : CuspForm (Gamma1 (N / ℓ)) k,
      (⇑h : UpperHalfPlane → ℂ) = ModularForm.heckeU k ℓ ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff h n = ModularFormClass.qCoeff f (ℓ * n)) ∧
      CuspForm.HasNebentypus ε' h := by sorry
