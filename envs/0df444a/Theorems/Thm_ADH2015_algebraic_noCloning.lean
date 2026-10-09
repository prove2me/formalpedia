-- Prove2me | Theorems.Thm_ADH2015_algebraic_noCloning
-- name    : ADH2015.algebraic_noCloning
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-09T10:05:44.315771+00:00
-- url     : https://prove2.me/theorems/c4e2919e-113c-4139-96dc-1d3962e02267
-- title:
--   Section 3.5 — algebraic no-cloning: operators represented on $E$ and on $\bar E$ commute on the code
-- statement:
--   Let $\mathcal H=\mathcal H_E\otimes\mathcal H_{\bar E}$ be finite-dimensional ($E$ the erased part, $\bar E$ the retained part) and let $\mathcal H_{\mathcal C}\subseteq\mathcal H$ be a code subspace. An operator $O$ **acts within** $\mathcal H_{\mathcal C}$ if $O$ and $O^\dagger$ both map $\mathcal H_{\mathcal C}$ into itself. It **has a representation on $\bar E$** if some $O_{\bar E}=\mathbb 1_E\otimes Y$ satisfies $O_{\bar E}|\tilde\psi\rangle=O|\tilde\psi\rangle$ and $O_{\bar E}^\dagger|\tilde\psi\rangle=O^\dagger|\tilde\psi\rangle$ for all $|\tilde\psi\rangle\in\mathcal H_{\mathcal C}$ (and analogously on $E$, with $X\otimes\mathbb 1_{\bar E}$). Then:
--   1. if $O_1$ and $O_2$ act within $\mathcal H_{\mathcal C}$, $O_1$ has a representation on $\bar E$ and $O_2$ has a representation on $E$, then $O_1O_2|\tilde\psi\rangle=O_2O_1|\tilde\psi\rangle$ for every $|\tilde\psi\rangle\in\mathcal H_{\mathcal C}$;
--   2. for any set $S$ of operators each of which acts within $\mathcal H_{\mathcal C}$ and has representations both on $E$ and on $\bar E$, any two elements of $S$ commute on $\mathcal H_{\mathcal C}$.
--
--   In particular a non-abelian algebra of logical operators cannot be represented both on $E$ and on $\bar E$: quantum information about a non-commuting set of observables cannot be accessible from two complementary subsystems at once.
-- source:
--   A. Almheiri, X. Dong, D. Harlow, Bulk Locality and Quantum Error Correction in AdS/CFT, JHEP 04 (2015) 163, https://arxiv.org/abs/1411.7041v3, Section 3.5, paragraph following the two-qubit example ('algebraic no-cloning theorem': a non-abelian subalgebra represented on Ē cannot be represented on E; proof via the commutator of two elements, one represented on E and one on Ē)

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker

namespace ADH2015

theorem algebraic_noCloning {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq e]
    [DecidableEq ē] (C : Submodule ℂ (e × ē → ℂ)) :
    (∀ O₁ O₂ : Matrix (e × ē) (e × ē) ℂ, ActsWithin C O₁ → ActsWithin C O₂ →
      HasRepOnBar C O₁ → HasRepOnE C O₂ →
      ∀ v ∈ C, O₁ *ᵥ (O₂ *ᵥ v) = O₂ *ᵥ (O₁ *ᵥ v)) ∧
    (∀ S : Set (Matrix (e × ē) (e × ē) ℂ),
      (∀ O ∈ S, ActsWithin C O ∧ HasRepOnBar C O ∧ HasRepOnE C O) →
      ∀ O₁ ∈ S, ∀ O₂ ∈ S, ∀ v ∈ C, O₁ *ᵥ (O₂ *ᵥ v) = O₂ *ᵥ (O₁ *ᵥ v)) := by sorry

end ADH2015
