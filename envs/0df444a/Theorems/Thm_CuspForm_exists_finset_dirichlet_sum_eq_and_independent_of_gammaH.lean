-- Prove2me | Theorems.Thm_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH
-- name    : CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/3877d5a7-0133-55d7-b626-526fc13dfdf4
-- title:
--   Nebentypus decomposition of cusp forms for Γ_H(M)
-- statement:
--   Fix a natural number $M$ with $M \neq 0$, a subgroup $H \leq (\mathbb{Z}/M)^{\times}$ and a weight $k \in \mathbb{Z}$, and let $\Gamma_H(M) \leq \mathrm{SL}_2(\mathbb{Z})$ be [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of those $\gamma \in \Gamma_0(M)$ whose associated unit of $\mathbb{Z}/M$ — the lower-right entry reduced mod $M$, with inverse the reduction of the upper-left entry — lies in $H$. The statement is a conjunction of two assertions about cusp forms of weight $k$ for $\Gamma_H(M)$. First, for every such cusp form $f$ there exist a finite set $s$ of Dirichlet characters modulo $M$ with values in $\mathbb{C}$ and an assignment $\varepsilon \mapsto f_\varepsilon$ of cusp forms of weight $k$ for $\Gamma_H(M)$ such that: each $\varepsilon \in s$ is trivial on $H$, i.e. $\varepsilon(d) = 1$ for every unit $d \in H$; each $f_\varepsilon$ with $\varepsilon \in s$ satisfies the nebentypus relation $f_\varepsilon \mid[k] \sigma = \varepsilon(d_\sigma) \, f_\varepsilon$ for all $\sigma \in \Gamma_0(M)$, where $\sigma$ acts through its image in $\mathrm{GL}_2(\mathbb{R})$ by the weight-$k$ slash action and $d_\sigma$ is the $(1,1)$ entry of $\sigma$ reduced mod $M$; and $f = \sum_{\varepsilon \in s} f_\varepsilon$ as functions on the upper half-plane. Second, for every finite set $s$ of Dirichlet characters modulo $M$ and every family $\varepsilon \mapsto g_\varepsilon$ of cusp forms of weight $k$ for $\Gamma_H(M)$ such that each $g_\varepsilon$, $\varepsilon \in s$, satisfies the same nebentypus relation with character $\varepsilon$, the vanishing $\sum_{\varepsilon \in s} g_\varepsilon = 0$ of the sum of the underlying functions forces $g_\varepsilon = 0$ for every $\varepsilon \in s$.
--
--   This is the isotypic decomposition $S_k(\Gamma_H(M)) = \bigoplus_{\varepsilon|_H = 1} S_k(M, \varepsilon)$ for the action of the finite abelian group $\Gamma_0(M)/\Gamma_H(M) \cong (\mathbb{Z}/M)^{\times}/H$ by diamond operators, together with the linear independence of the nebentypus components. It is used in the construction of a basis of primitive forms for $\Gamma_H(M)$ compatible with the Hecke, diamond and $U$-operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH.lean

import Definitions.Def_CohCarrier_Level
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    (∀ f : CuspForm (CohCarrier.GammaH M H) k,
      ∃ (s : Finset (DirichletCharacter ℂ M)) (fε : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k),
        (∀ ε ∈ s, ∀ d : (ZMod M)ˣ, d ∈ H → ε (d : ZMod M) = 1) ∧
        (∀ ε ∈ s, ∀ σ : CongruenceSubgroup.Gamma0 M,
          ⇑(fε ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
            ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(fε ε)) ∧
        ⇑f = ∑ ε ∈ s, ⇑(fε ε)) ∧
    (∀ (s : Finset (DirichletCharacter ℂ M)) (g : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k),
      (∀ ε ∈ s, ∀ σ : CongruenceSubgroup.Gamma0 M,
          ⇑(g ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
            ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(g ε)) →
      (∑ ε ∈ s, ⇑(g ε)) = 0 → ∀ ε ∈ s, g ε = 0) := by sorry
