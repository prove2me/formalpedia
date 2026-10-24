-- Prove2me | Theorems.Thm_FCP_Jacobian_etale_and_flat_aeval_of_isUnit_jacobian
-- name    : FCP.Jacobian.etale_and_flat_aeval_of_isUnit_jacobian
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T06:48:22.998305+00:00
-- url     : https://prove2.me/theorems/dc81295d-b865-419f-a6ba-0a3ed6a8e1bc
-- title:
--   A unit polynomial Jacobian makes substitution étale and flat
-- statement:
--   Let $k$ be any commutative ring, let $n\ge0$, and let $F=(F_1,\ldots,F_n)$ be a tuple of polynomials in $k[X_1,\ldots,X_n]$. Assume that the determinant of the Jacobian matrix $(\partial F_i/\partial X_j)_{i,j}$ is a unit in the polynomial ring. Then the actual substitution homomorphism
--
--   $$k[X_1,\ldots,X_n]\longrightarrow k[X_1,\ldots,X_n],\qquad X_i\longmapsto F_i,$$
--
--   is étale and flat. The algebra and module structures in these conclusions are induced by substitution, even though source and target have the same underlying ring. The statement includes dimension zero and needs no field or characteristic-zero assumption.
--
--   This standard Jacobian-to-étaleness bridge is a reusable input for studying the existing two-variable Jacobian-conjecture target. It does not assert birationality or existence of a polynomial inverse.
-- source:
--   Polynomial Kähler differentials and the étale-coordinate criterion. Uses the actual accepted public theorem Algebra.FormallySmooth.etale_aeval_of_basis_kaehlerDifferential (9d18d03b-da7c-5f5e-bdf9-caa8b756ff12); its accepted formal proof was retrieved and inspected. The basis argument and flatness implication are checked against the fixed Mathlib revision. This is the standard Jacobian/étale-coordinate criterion, a necessary reusable intermediate result for audited mission target FCP.Jacobian.jacobian_two_variables (54fd299c-e9b0-490c-97f0-4cbef88de8fc). No claim of resolving the conjecture is made.

import Mathlib
import Definitions.Def_FCP_Jacobian

theorem FCP.Jacobian.etale_and_flat_aeval_of_isUnit_jacobian {k : Type} [CommRing k] {n : ℕ}
    (F : FCP.Jacobian.PolyMap k n) (hF : IsUnit (FCP.Jacobian.jacobian F).det) :
    (MvPolynomial.aeval (R := k) F).toRingHom.Etale ∧ (MvPolynomial.aeval (R := k) F).toRingHom.Flat := by sorry
