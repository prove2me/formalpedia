-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal
-- name    : CerednikDrinfeld.exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/fc222295-209f-5b92-bda7-9d0c540f1f2d
-- title:
--   Complete unramified r-rings are Witt rings, compatibly with Frobenius
-- statement:
--   Let $r$ be a prime and let $Onr$ be an integral domain of characteristic $0$ containing an element $\varpi$ with $(\varpi) = (r)$ as ideals, such that $Onr$ is $(\varpi)$-adically complete (in the sense of Mathlib's `IsAdicComplete`, i.e. Hausdorff and complete for the $(\varpi)$-adic filtration), the ideal $(\varpi)$ is maximal, and every monic polynomial over $Onr$ of positive natural degree has some $x \in Onr$ with value in $(\varpi)$; let moreover $Fr$ be a ring automorphism of $Onr$ with $Fr(x) - x^{r} \in (\varpi)$ for all $x$. The conclusion asserts the existence of a type $k$ carrying a field structure, of characteristic $r$ and algebraically closed, of a ring isomorphism $e \colon W_r(k) \xrightarrow{\sim} Onr$ from the ring of $r$-typical Witt vectors of $k$, and of a ring homomorphism $q \colon Onr \to k$, such that $e(F x) = Fr(e\,x)$ for all $x \in W_r(k)$, where $F$ is the Witt vector Frobenius, $q$ is surjective with kernel exactly $(\varpi)$, and $q(e\,x) = x_0$, the zeroth Witt coefficient of $x$, for all $x \in W_r(k)$.
--
--   This is the classical structure theorem for strict $r$-rings with perfect residue ring, in the form: a complete discrete-valuation-like ring unramified over $\mathbb{Z}_r$ with algebraically closed residue field is the Witt ring of its residue field, and any lift of the $r$-power map corresponds to the Witt vector Frobenius. It is used in the Cerednik–Drinfeld part of the development, in the identification of the group acting on the relevant moduli package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal
    (r : ℕ) [Fact r.Prime]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr]
    (ϖ : Onr) (hϖ : Ideal.span {ϖ} = Ideal.span {((r : ℕ) : Onr)})
    (hcomplete : IsAdicComplete (Ideal.span {ϖ}) Onr)
    (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hclosed : ∀ q : Polynomial Onr, q.Monic → 0 < q.natDegree → ∃ x : Onr, Polynomial.eval x q ∈ Ideal.span {ϖ})
    (Fr : Onr ≃+* Onr) (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {ϖ}) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k r) (_ : IsAlgClosed k) (e : WittVector r k ≃+* Onr)
      (q : Onr →+* k),
      (∀ x : WittVector r k, e (WittVector.frobenius x) = Fr (e x)) ∧
      Function.Surjective q ∧ RingHom.ker q = Ideal.span {ϖ} ∧
      (∀ x : WittVector r k, q (e x) = x.coeff 0) := by sorry
