-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_SignatureOrthogonalNonpositive_signature_orthogonal_nonpositive
-- name    : CountingMatroid.Analysis.SignatureOrthogonalNonpositive.signature_orthogonal_nonpositive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T09:43:37.89661+00:00
-- url     : https://prove2.me/theorems/ef23ac00-fcaa-412f-a6da-32aa02415af8
-- title:
--   Nonpositivity orthogonal to a positive vector
-- statement:
--   Let $V$ be a finite-dimensional real vector space and $Q$ a quadratic form on $V$ with positive index at most one. Thus a subspace on which $Q$ is positive definite has dimension at most one. If $Q(e)>0$ and $B_Q(e,v)=0$, where $B_Q$ is the symmetric bilinear form associated with $Q$, then $Q(v)\leq0$.
--
--   Orthogonality here is with respect to $B_Q$. This is the quadratic-form principle used in the transport Hessian argument.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SignatureOrthogonalNonpositive.lean#L14-L69 — signature_orthogonal_nonpositive; the quadratic-form argument used in the proof of Lemma 3.2, p. 6.

import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

set_option autoImplicit false

/-!
The elementary real quadratic-form step in the transport Hessian argument:
a form with at most one positive direction is nonpositive on the orthogonal
complement of any vector where the form is positive.
-/

namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SignatureOrthogonalNonpositive

theorem CountingMatroid.Analysis.SignatureOrthogonalNonpositive.signature_orthogonal_nonpositive {V : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V)
    (hsig : sigPos Q ≤ 1) (e v : V) (he : 0 < Q e)
    (horth : Q.associated e v = 0) : Q v ≤ 0 := by sorry
