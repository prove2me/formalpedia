-- Prove2me | Theorems.Thm_BrauerIdem_Splitting_theorem_14
-- name    : BrauerIdem.Splitting.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:04.061639+00:00
-- url     : https://prove2.me/theorems/11d892bb-637d-426e-a46e-acee35f8b5c7
-- title:
--   Theorem 14, p. 9 — ūX_n(ℓ) = −ū is uniquely solvable in orbit sums with coefficients in K, and 1 + X_n(ℓ) is the splitting idempotent of J̄_n(ℓ)
-- statement:
--   Let $\ell<n$ with $n-\ell$ even. For each simultaneous $\mathfrak S_n$-orbit $O$ of diagrams with at most $\ell$ propagating lines, write $D_O$ for its unnormalised diagram sum. There is exactly one family of coefficients $c_O\in F=\mathbb Q(\delta)$ such that, with $X=\sum_Oc_OD_O$,
--
--   $$
--   \bar uX=-\bar u.
--   $$
--
--   Every $c_O$ of this family lies in $K$. Moreover $\varphi=1+X$ is the splitting idempotent for $J_n(\ell)$: $\varphi-1\in J_n(\ell)$, $\varphi J_n(\ell)=J_n(\ell)\varphi=0$, $\varphi^2=\varphi$, and $\varphi$ is central. It therefore corresponds to the split short exact sequence $0\to J_n(\ell)\to B_n\to B_n/J_n(\ell)\to0$.
--
--   The theorem turns a single diagram equation into a canonical central idempotent with coefficients in the specialization-friendly ring $K$.
--
--   **Formalization Note** The Lean equation uses the unnormalised cup diagram $u$ instead of $\bar u=\delta^{-(n-\ell)/2}u$; these equations have the same solutions over $F$. Its orbit basis is indexed by diagram orbits rather than the equivalent Spore tableaux. Evenness of $n-\ell$ is a disclosed domain condition for the displayed $\bar u$ product. The splitting conditions are stated over $F$, with membership of every constructed coefficient in $K$ stated separately.
-- source:
--   King, Martin, Parker, On central idempotents in the Brauer algebra, arXiv:1609.01183v1, p. 9, Theorem 14

import Mathlib
import Definitions.Def_BrauerIdem_Splitting_Brauer

namespace BrauerIdem.Splitting

/-- King–Martin–Parker, Theorem 14, p. 9. -/
theorem theorem_14 (n l : ℕ) (hl : l < n) (hpar : Even (n - l)) :
    ∃ c : OrbitIdx n l → F,
      (∀ c' : OrbitIdx n l → F,
        bmul (basis (uDiag n l)) (Xof c') = -basis (uDiag n l) ↔ c' = c) ∧
      (∀ O, c O ∈ Kring) ∧
      IsSplittingIdempotent (Jideal n l) (one n + Xof c) ∧
      bmul (one n + Xof c) (one n + Xof c) = one n + Xof c ∧
      (∀ x : Br n, bmul (one n + Xof c) x = bmul x (one n + Xof c)) := by sorry

end BrauerIdem.Splitting
