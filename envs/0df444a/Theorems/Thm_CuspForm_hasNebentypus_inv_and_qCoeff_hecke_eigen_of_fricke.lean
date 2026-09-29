-- Prove2me | Theorems.Thm_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke
-- name    : CuspForm.hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/c1ac8f85-a77a-5577-b548-b8fbb3d101c6
-- title:
--   Fricke transform inverts nebentypus and twists Tₚ-eigenvalues
-- statement:
--   Let $M \geq 1$ and $k \in \mathbb{Z}$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and let $g, h$ be cusp forms of weight $k$ for $\Gamma_1(M)$. Assume that $g$ has nebentypus $\varepsilon$, in the sense that for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ and every $\tau \in \mathfrak{H}$ one has $g(\gamma \cdot \tau) = \varepsilon(\gamma_{11} \bmod M)\,(\gamma_{10}\tau + \gamma_{11})^k\, g(\tau)$, where indices refer to the bottom row of $\gamma$. Assume further that $h$ is a Fricke transform of $g$: for all $\tau, \tau' \in \mathfrak{H}$ with $\tau' \cdot (M\tau) = -1$ one has $g(\tau') = \tau^k h(\tau)$. Then two conclusions hold. First, $h$ has nebentypus $\varepsilon^{-1}$, in the same sense. Second, for every prime $p$ not dividing $M$ and every $\lambda \in \mathbb{C}$, writing $a_n =$ `qCoeff` $g\,n$ and $b_n =$ `qCoeff` $h\,n$ for the coefficients of the $q$-expansions of width $1$: if $a_{pn} + \varepsilon(p)\,p^{k-1}\,[p \mid n]\,a_{n/p} = \lambda a_n$ for all $n \in \mathbb{N}$ (the bracket denoting the term $a_{n/p}$ when $p \mid n$ and $0$ otherwise), then $b_{pn} + \varepsilon^{-1}(p)\,p^{k-1}\,[p \mid n]\,b_{n/p} = \varepsilon^{-1}(p)\,\lambda\, b_n$ for all $n \in \mathbb{N}$.
--
--   This is the coefficient-level form of the operator identities $W_M \langle d \rangle W_M^{-1} = \langle d \rangle^{-1}$ and $W_M T_p W_M^{-1} = \langle p \rangle^{-1} T_p$ for the Fricke matrix $W_M = \begin{pmatrix} 0 & -1 \\ M & 0\end{pmatrix}$ acting on $S_k(\Gamma_1(M))$, as in Atkin–Li: the Fricke transform of a form of nebentypus $\varepsilon$ which is a $T_p$-eigenform with eigenvalue $\lambda$ has nebentypus $\bar\varepsilon$ and $T_p$-eigenvalue $\bar\varepsilon(p)\lambda$. It is used in the treatment of primitive forms on $\Gamma_1(M)$, in [`CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm`](thm.html#CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g h : CuspForm (Gamma1 M) k)
    (hg : CuspForm.HasNebentypus ε g)
    (hh : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
      g τ' = (τ : ℂ) ^ k * h τ) :
    CuspForm.HasNebentypus ε⁻¹ h ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ lam : ℂ,
        (∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          lam * ModularFormClass.qCoeff g n) →
        ∀ n : ℕ, ModularFormClass.qCoeff h (p * n) +
            ε⁻¹ (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff h (n / p) else 0) =
          ε⁻¹ (p : ZMod M) * lam * ModularFormClass.qCoeff h n := by sorry
