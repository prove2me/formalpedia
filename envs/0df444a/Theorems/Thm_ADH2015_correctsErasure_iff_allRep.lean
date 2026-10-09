-- Prove2me | Theorems.Thm_ADH2015_correctsErasure_iff_allRep
-- name    : ADH2015.correctsErasure_iff_allRep
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-09T10:04:28.502417+00:00
-- url     : https://prove2.me/theorems/8b2170af-76f9-4000-9943-356b7a19716f
-- title:
--   Section 3.2, Eqs. (3.19) ⟺ (3.21) — $P X_E P\propto P$ for every $X_E$ iff every logical operator has a representation on $\bar E$
-- statement:
--   Let $\mathcal H=\mathcal H_E\otimes\mathcal H_{\bar E}$ be finite-dimensional ($E$ the erased part, $\bar E$ the retained part) and let $\mathcal H_{\mathcal C}\subseteq\mathcal H$ be a code subspace. An operator $O$ **acts within** $\mathcal H_{\mathcal C}$ if $O$ and $O^\dagger$ both map $\mathcal H_{\mathcal C}$ into itself. It **has a representation on $\bar E$** if some $O_{\bar E}=\mathbb 1_E\otimes Y$ satisfies $O_{\bar E}|\tilde\psi\rangle=O|\tilde\psi\rangle$ and $O_{\bar E}^\dagger|\tilde\psi\rangle=O^\dagger|\tilde\psi\rangle$ for all $|\tilde\psi\rangle\in\mathcal H_{\mathcal C}$ (and analogously on $E$, with $X\otimes\mathbb 1_{\bar E}$). Then the following are equivalent:
--   1. (Eq. (3.19)) for every operator $X_E$ on $E$ there is $c\in\mathbb C$ with $\langle\tilde\psi'|X_E\otimes\mathbb 1_{\bar E}|\tilde\psi\rangle=c\,\langle\tilde\psi'|\tilde\psi\rangle$ for all code states, i.e. the projection of $X_E$ onto the code subspace is proportional to the identity;
--   2. (Eq. (3.21)) every operator acting within $\mathcal H_{\mathcal C}$ has a representation on $\bar E$.
--
--   This is the operator form of the erasure-correction condition: every logical operator can be implemented on the surviving subsystem $\bar E$ alone exactly when operators on the erased subsystem $E$ cannot distinguish code states. It is the special case of the basic theorem of operator-algebra quantum error correction in which the logical algebra is the full operator algebra of the code subspace.
--
--   **Formalization Note** The source cites (3.19) as equivalent to correctability of the erasure of $E$ (the existence of a recovery unitary, Eqs. (3.14)–(3.18), from refs. [26], [28]); that equivalence is not formalized here. Condition (3.19), $\langle\tilde\imath|X_E|\tilde\jmath\rangle=\delta_{ij}C(X)$ in an orthonormal basis, is stated basis-free as $\langle\tilde\psi'|X_E\tilde\psi\rangle=c\,\langle\tilde\psi'|\tilde\psi\rangle$ for one constant $c$ and all code vectors.
-- source:
--   A. Almheiri, X. Dong, D. Harlow, Bulk Locality and Quantum Error Correction in AdS/CFT, JHEP 04 (2015) 163, https://arxiv.org/abs/1411.7041v3, Section 3.2, Eq. (3.19), Eq. (3.21) and the paragraph following (3.21) ('In fact the converse of this statement also holds')

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker

namespace ADH2015

theorem correctsErasure_iff_allRep {e ē : Type*} [Fintype e] [Fintype ē] [DecidableEq e]
    [DecidableEq ē] (C : Submodule ℂ (e × ē → ℂ)) :
    CorrectsErasureOfE C ↔ ∀ O : Matrix (e × ē) (e × ē) ℂ, ActsWithin C O → HasRepOnBar C O := by sorry

end ADH2015
