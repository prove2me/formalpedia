-- Prove2me | Theorems.Thm_ADH2015_oaqec_basic_theorem
-- name    : ADH2015.oaqec_basic_theorem
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T10:06:20.447069+00:00
-- url     : https://prove2.me/theorems/c731c032-2f49-4e68-ae2e-83a551bd6721
-- title:
--   Section 3.5 / Appendix B — the basic theorem of operator-algebra quantum error correction
-- statement:
--   Let $\mathcal H=\mathcal H_E\otimes\mathcal H_{\bar E}$ be finite-dimensional ($E$ the erased part, $\bar E$ the retained part) and let $\mathcal H_{\mathcal C}\subseteq\mathcal H$ be a code subspace. An operator $O$ **acts within** $\mathcal H_{\mathcal C}$ if $O$ and $O^\dagger$ both map $\mathcal H_{\mathcal C}$ into itself. It **has a representation on $\bar E$** if some $O_{\bar E}=\mathbb 1_E\otimes Y$ satisfies $O_{\bar E}|\tilde\psi\rangle=O|\tilde\psi\rangle$ and $O_{\bar E}^\dagger|\tilde\psi\rangle=O^\dagger|\tilde\psi\rangle$ for all $|\tilde\psi\rangle\in\mathcal H_{\mathcal C}$ (and analogously on $E$, with $X\otimes\mathbb 1_{\bar E}$). Let $O$ act within $\mathcal H_{\mathcal C}$ (Eq. (3.26)). Then $O$ has a representation $O_{\bar E}$ on $\bar E$ (Eq. (3.27)) **if and only if** $O$ commutes, on the code subspace, with every operator on $E$ (Eq. (3.28)):
--   $$\langle\tilde\psi'|\,[O,\;X_E\otimes\mathbb 1_{\bar E}]\,|\tilde\psi\rangle=0\qquad\text{for all operators }X_E\text{ on }E\text{ and all }|\tilde\psi\rangle,|\tilde\psi'\rangle\in\mathcal H_{\mathcal C}.$$
--
--   The theorem characterizes, by a checkable commutation condition, which logical operators survive the erasure of $E$. Applied to all operators acting within the code subspace it recovers the erasure-correction criterion of Section 3.2, and it underlies the algebraic no-cloning property and the holographic interpretation of bulk reconstruction.
--
--   **Formalization Note** The source states (3.28) as $\langle\tilde\imath|[O,X_E]|\tilde\jmath\rangle=0$ for an orthonormal basis $|\tilde\imath\rangle$ of the code subspace; by sesquilinearity this is the same as vanishing on all pairs of code vectors, which is how it is stated here (no basis is fixed).
-- source:
--   A. Almheiri, X. Dong, D. Harlow, Bulk Locality and Quantum Error Correction in AdS/CFT, JHEP 04 (2015) 163, https://arxiv.org/abs/1411.7041v3, Section 3.5, Theorem (Eqs. (3.26)–(3.28)); proof in Appendix B, Eqs. (B.1)–(B.17)

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker

namespace ADH2015

theorem oaqec_basic_theorem {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq e]
    [DecidableEq ē] (C : Submodule ℂ (e × ē → ℂ)) (O : Matrix (e × ē) (e × ē) ℂ)
    (hO : ActsWithin C O) :
    HasRepOnBar C O ↔
      ∀ X : Matrix e e ℂ, ∀ v ∈ C, ∀ w ∈ C,
        star w ⬝ᵥ ((O * (X ⊗ₖ (1 : Matrix ē ē ℂ)) - (X ⊗ₖ (1 : Matrix ē ē ℂ)) * O) *ᵥ v) = 0 := by sorry

end ADH2015
