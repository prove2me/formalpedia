-- Prove2me | Theorems.Thm_ErasureQTanner_lemma_13
-- name    : ErasureQTanner.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:10:02.891212+00:00
-- url     : https://prove2.me/theorems/9d135c2e-a57e-4529-a62c-4094df07525a
-- title:
--   Lemma 13 — rank expressions for the covered dimension
-- statement:
--   Let $C\subseteq\mathbb F_2^n$ be linear, $G\in\mathbb F_2^{\dim C\times n}$ a generator matrix and $H\in\mathbb F_2^{(n-\dim C)\times n}$ a parity-check matrix. For every pattern $x$,
--   $$\dim S_C(x)=\dim C-\mathrm{rank}\,G_{\bar x}=\mathrm{wt}(x)-\mathrm{rank}\,H_x,$$
--   where $A_y$ restricts $A$ to the columns in the support of $y$. It translates between the erasure events of a code and of its dual.
--
--   Differences from the source:
--   - encoding: identities in $\mathbb N$ → identities in $\mathbb Z$; reason: avoids truncated subtraction; the printed identities have non-negative right-hand sides
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), Lemma 13, p.20

import Mathlib
import Definitions.Def_ErasureQTanner_covered
import Definitions.Def_ErasureQTanner_HX

set_option autoImplicit false

namespace ErasureQTanner

/-- **Lemma 13.** Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.20: for a linear code `C ⊆ F₂ⁿ` with generator matrix `G ∈ F₂^{dim C×n}` and
parity-check matrix `H ∈ F₂^{(n−dim C)×n}`, for every `x`, `dim S_C(x) = dim C − rank G_x̄ = wt(x) − rank H_x`, where `A_y` restricts `A`
to the columns in the support of `y`.

**Formalization Note.** The identities are stated in `ℤ`, so no truncated subtraction occurs. -/
theorem lemma_13 {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (G : Matrix (Fin (Module.finrank (ZMod 2) C)) (Fin n) (ZMod 2)) (hG : C = checkRows G)
    (H : Matrix (Fin (n - Module.finrank (ZMod 2) C)) (Fin n) (ZMod 2)) (hH : C = checkKer H)
    (x : Fin n → Bool) :
    (Module.finrank (ZMod 2) (covered C x) : ℤ) =
        (Module.finrank (ZMod 2) C : ℤ) -
          (G.submatrix id (Subtype.val : {i // x i = false} → Fin n)).rank ∧
      (Module.finrank (ZMod 2) (covered C x) : ℤ) =
        ((Finset.univ.filter fun i => x i = true).card : ℤ) -
          (H.submatrix id (Subtype.val : {i // x i = true} → Fin n)).rank := by sorry

end ErasureQTanner
