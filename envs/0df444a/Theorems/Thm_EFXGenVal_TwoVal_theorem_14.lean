-- Prove2me | Theorems.Thm_EFXGenVal_TwoVal_theorem_14
-- name    : EFXGenVal.TwoVal.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:06.649135+00:00
-- url     : https://prove2.me/theorems/0f173eda-12c8-4058-afde-9a13c3fe5f19
-- title:
--   Theorem 14, p. 12 — every partial EFX allocation has an EFX allocation larger in the partition leximin order
-- statement:
--   Let the agents have normalized, monotone, non-degenerate valuations, each agent having one of two valuations: $v_a$ on a nonempty class $N_a$ and $v_b$ on the nonempty class $N_b=N\setminus N_a$. Let $X$ be a partial EFX allocation, i.e. an EFX allocation that leaves at least one item unallocated. Then there exists an EFX allocation $Y$ with
--   $$Y\succ_{\mathrm{p.lexmin}}X,$$
--   that is, $\psi(Y)$ is strictly lexicographically larger than $\psi(X)$, where $\psi(X)$ lists the $v_a$-values of the bundles of $N_a$ in increasing order followed by the $v_b$-values of the bundles of $N_b$ in increasing order.
--
--   This is the progress step of the paper's potential-function argument; since there are finitely many allocations, iterating it from the empty allocation reaches a complete EFX allocation.
--
--   **Formalization Note** $Y$ may itself be partial or complete. The partition leximin order is the strict lexicographic order (`List.Lex (· < ·)`) on two lists of the same length $n$, so $Y=X$ is never a witness. Both classes are assumed nonempty because the page's notation $N_a=\{a_0,\dots\}$, $N_b=\{b_0,\dots\}$ and the proof (which names $a_0$ and $b_0$) presuppose it. $v_a=v_b$ is allowed.
-- source:
--   Mahara, Extension of Additive Valuations to General Valuations on the Existence of EFX, arXiv:2107.09901v2, §4, Theorem 14, p. 12

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXGenVal_TwoVal_Setting

namespace EFXGenVal.TwoVal

open LittleCharity.EFX

theorem theorem_14 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v) (hnd : IsNonDegenerate v)
    (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, v i = va) (hB : ∀ i ∉ A, v i = vb)
    (hAne : A.Nonempty) (hBne : Aᶜ.Nonempty)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X)
    (hpool : (pool X).Nonempty) (hEFX : IsEFX v X) :
    ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ IsEFX v Y ∧
      PLexGT va vb A Y X := by sorry

end EFXGenVal.TwoVal
