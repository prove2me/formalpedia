-- Prove2me | Theorems.Thm_Diaz_quadric_trdeg_two
-- name    : Diaz.quadric_trdeg_two
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T09:29:11.557253+00:00
-- url     : https://prove2.me/theorems/04ee387f-5b1b-4716-a2b8-79ba1a34244b
-- title:
--   The independence upgrade at the Diaz-locus quadric
-- statement:
--   **Source.** The hypothesis `hIU` is an independence upgrade that Carlo Perassi uses and that **is not his own**: it is stated explicitly in Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, p. 593, immediately after Theorem 15.30, in the form that $\mathbb Q$-linearly independent elements of $\mathcal L$ generating a field of transcendence degree one satisfy $Q(\lambda_1,\dots,\lambda_n)\ne0$ for every non-zero homogeneous rational $Q$ of degree two. Carlo Perassi derives it from Roy and Waldschmidt's *Théorème 0.2*.
--
--   **The cited lemma, as carried.** Let $\lambda_1,\dots,\lambda_n\in\mathcal L$ be linearly independent over $\mathbb Q$ and let $P\in\mathbb Q[X_1,\dots,X_n]$ be a non-zero homogeneous polynomial of degree at most two with $P(\lambda_1,\dots,\lambda_n)=0$. Then $\operatorname{trdeg}_{\mathbb Q}\mathbb Q(\lambda_1,\dots,\lambda_n)\ge2$.
--
--   As stated here, for logarithms of algebraic numbers, it is the case of $\mathbb Q$-linearly independent coordinates of Théorème 0.2 of D. Roy and M. Waldschmidt, Ann. Sci. École Norm. Sup. (4) 30 (1997), p. 755: there the only subspace defined over $\mathbb Q$ that contains the point is $\mathbb C^{n}$, which is not contained in the zero set of $P\ne0$. The sentence after Theorem 15.30 on p. 593 of Waldschmidt's book is its degree-two form in transcendence degree one. **It is carried as the explicit hypothesis `hIU` rather than asserted.** The node asserts only the consequence below.
--
--   **The consequence.** Let $K\subset\mathbb C$ be a subfield and let $u,v$ be such that $u,\overline u,v,\overline v$ are all logarithms of elements of $K$, with squared moduli rationally commensurable,
--   $$v\overline v \;=\; m\,(u\overline u),\qquad m\in\mathbb Q^\times,$$
--   and with $u,\overline u,v,\overline v$ linearly independent over $\mathbb Q$. Then
--   $$\operatorname{trdeg}_{\mathbb Q}\mathbb Q\bigl(u,\overline u,v,\overline v\bigr)\ \ge\ 2 .$$
--   This is Carlo Perassi's reading of the lemma on the Diaz locus: two Diaz candidates with rational squared-modulus ratio have a $\mathbb Q$-linearly independent conjugate quadruple (that independence is the mission's `Diaz.indep_quadruple`) lying on the rational quadric $mX_1X_2-X_3X_4=0$, so the lemma applies at full strength.
--
--   **What is verified.** The instantiation itself: that $P=mX_1X_2-X_3X_4$ is a non-zero homogeneous polynomial of degree two over $\mathbb Q$ (non-zero because its value at $(1,1,0,0)$ is $m\ne0$), that it vanishes at the quadruple exactly when $v\overline v=m\,u\overline u$, and that the $\mathbb Q$-linear independence hypothesis of the lemma is the one supplied. Everything deeper sits inside `hIU`.
--
--   **Formalization note.** The lemma is carried over `Fin n` with `MvPolynomial (Fin n) ℚ`, `MvPolynomial.IsHomogeneous`, and evaluation by `MvPolynomial.aeval`; transcendence degree is `Algebra.trdeg ℚ` of `Algebra.adjoin ℚ` of the relevant set. `#print axioms` on the submitted proof: `[propext, Classical.choice, Quot.sound]`.

import Mathlib

open ComplexConjugate

theorem Diaz.quadric_trdeg_two {K : Subfield ℂ}
    (hIU : ∀ (n : ℕ) (l : Fin n → ℂ) (P : MvPolynomial (Fin n) ℚ),
      (∀ i, Complex.exp (l i) ∈ K) →
      (∀ c : Fin n → ℚ, (∑ i, (c i : ℂ) * l i = 0) → c = 0) →
      P ≠ 0 → (∃ d, d ≤ 2 ∧ P.IsHomogeneous d) →
      MvPolynomial.aeval l P = 0 →
      2 ≤ Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ (Set.range l)))
    {u v : ℂ} {m : ℚ}
    (hu : Complex.exp u ∈ K) (huc : Complex.exp (conj u) ∈ K)
    (hv : Complex.exp v ∈ K) (hvc : Complex.exp (conj v) ∈ K)
    (hm : m ≠ 0) (hquad : v * conj v = (m : ℂ) * (u * conj u))
    (hindep : ∀ a b c d : ℚ,
      (a : ℂ) * u + (b : ℂ) * conj u + (c : ℂ) * v + (d : ℂ) * conj v = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) :
    2 ≤ Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({u, conj u, v, conj v} : Set ℂ)) := by sorry
