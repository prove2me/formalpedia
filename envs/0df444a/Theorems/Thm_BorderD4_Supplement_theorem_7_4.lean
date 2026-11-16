-- Prove2me | Theorems.Thm_BorderD4_Supplement_theorem_7_4
-- name    : BorderD4.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:04:12.447381+00:00
-- url     : https://prove2.me/theorems/d2fe8900-ae79-4f8a-9d16-0a1a8674ec94
-- title:
--   Theorem 7.4 — $F[W_0]^\times/F^\times$ is free abelian of rank at most $\Delta$
-- statement:
--   Let $F$ be an algebraically closed field of characteristic $0$. Let $W_0\subseteq\mathbb A^N$ be an irreducible affine variety of degree $\Delta$ and dimension $d\ge1$. Then the group
--   $$F[W_0]^\times/F^\times$$
--   of units modulo constants is free abelian of rank at most $\Delta$.
--
--   This effective form of Samuel's unit theorem controls the nonconstant units on the variety obtained in the exact impossibility proof, Theorem 7.5.
--
--   **Formalization Note** $W_0=V(p)$ for a prime ideal $p$, $F[W_0]=F[x]/p$, $\deg W_0$ is `BorderD4.HasDEG`, and $\dim W_0$ is the Krull dimension of $F[x]/p$. Free abelian of rank at most $\Delta$ is an isomorphism of the group, written additively, with $\mathbb Z^r$ for some $r\le\Delta$.
--
--   Differences from the source:
--   - encoding: W_0 ⊆ A^N irreducible of degree Δ and dimension d, F[W_0] → a prime ideal p with HasDEG p Δ, ringKrullDim (F[x]/p) = d, and F[W_0] = F[x]/p; reason: over an algebraically closed field W_0 ↦ I(W_0) is a bijection onto prime ideals and F[W_0] = F[x]/I(W_0)
--   - encoding: free abelian of rank at most Δ → ∃ r ≤ Δ, an additive group isomorphism Additive (F[W_0]^×/F^×) ≃ (Fin r → ℤ); reason: a free abelian group of finite rank r is isomorphic to ℤ^r
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 7.4, p.81; standing assumptions p.3 and §7, p.77; §2.2, p.31

import Mathlib
import Definitions.Def_BorderD4_HasDEG
import Definitions.Def_BorderD4_Supplement_unitsModConstants
set_option autoImplicit false

open MvPolynomial

namespace BorderD4.Supplement

/-- Theorem 7.4: a rank bound for the group of units modulo constants.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 7.4, p.81; standing assumptions p.3 (characteristic `0`) and §7, p.77 (`F` algebraically closed); degree, §2.2, p.31.

Let `W_0 ⊆ A^N` be an irreducible affine variety of degree `∆` and dimension `d ≥ 1`. Then `F[W_0]^×/F^×` is a free
abelian group of rank at most `∆`.

**Formalization Note** `W_0 = V(p)` is given by its prime ideal `p = I(W_0) ⊆ F[x_1, …, x_N]` (over an algebraically
closed field every prime is the ideal of an irreducible variety); `F[W_0] = F[x]/p`; `deg W_0 = ∆` is the published
`BorderD4.HasDEG p ∆`; `dim W_0` is the Krull dimension of `F[x]/p`. "Free abelian of rank at most `∆`" is a group
isomorphism of the quotient, written additively, with `ℤ^r` for some `r ≤ ∆`. -/
theorem theorem_7_4 {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] {N : ℕ}
    (p : Ideal (MvPolynomial (Fin N) F)) (hp : p.IsPrime) (Δ d : ℕ) (hΔ : BorderD4.HasDEG p Δ)
    (hdim : ringKrullDim (MvPolynomial (Fin N) F ⧸ p) = d) (hd : 1 ≤ d) :
    ∃ r : ℕ, r ≤ Δ ∧
      Nonempty (Additive (unitsModConstants F (MvPolynomial (Fin N) F ⧸ p)) ≃+ (Fin r → ℤ)) := by sorry

end BorderD4.Supplement
