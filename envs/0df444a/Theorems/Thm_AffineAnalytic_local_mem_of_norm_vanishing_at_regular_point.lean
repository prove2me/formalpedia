-- Prove2me | Theorems.Thm_AffineAnalytic_local_mem_of_norm_vanishing_at_regular_point
-- name    : AffineAnalytic.local_mem_of_norm_vanishing_at_regular_point
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-04T08:17:10.387089+00:00
-- url     : https://prove2.me/theorems/9c4e05d1-9433-4fdc-b067-407679064fff
-- title:
--   Norm-local vanishing gives algebraic local membership at a regular point
-- statement:
--   Let $K$ be a complete, algebraically closed, nontrivially normed field of characteristic zero, let $\sigma$ be a finite set, and put $A=K[X_j\mid j\in\sigma]$. Let $I\subseteq A$ be an ideal and $a\in K^\sigma$ a common zero of $I$. Write
--   $$\mathfrak m_a=\ker(\operatorname{ev}_a),\qquad R=A_{\mathfrak m_a}/IA_{\mathfrak m_a}.$$
--   Assume that $R$ is a regular local ring. If a polynomial $P\in A$ vanishes on all common zeros of $I$ in some norm neighborhood of $a$, then
--   $$P/1\in IA_{\mathfrak m_a}.$$
--   Equivalently, there is a polynomial $H\in A$ such that $H(a)\ne0$ and $HP\in I$. Thus vanishing of a polynomial on the norm germ of the affine zero set at a regular rational point implies vanishing of its algebraic local-ring germ.
--
--   The common zero set need not be globally irreducible or smooth. The ideal is not assumed radical away from $a$; regularity is required of the actual localized quotient, so it rules out nonreduced structure at the point being studied. Empty coordinate sets and zero-dimensional local rings are included.
--
--   **Formalization Note.** The evaluation maximal ideal is supplied explicitly with its identification as the kernel of evaluation. The neighborhood hypothesis is an eventual implication in the ordinary norm topology of $K^\sigma$. This is the local-ring comparison underlying the smooth local-density argument in Platonov--Rapinchuk, Lemma 3.2. The source chapter works over locally compact fields; the stated complete-field extension is an explicit part of this Open obligation. In particular, it includes $\mathbb C_p$ without assuming local compactness. No group, projective coordinates, chosen analytic chart, or density conclusion is an input.
-- source:
--   V. Platonov and A. Rapinchuk, Algebraic Groups and Number Theory (1994), section 3.1, Lemma 3.2 and its proof, printed p.114, https://uva.theopenscholar.com/files/andrei-rapinchuk/files/agnt_english.pdf . The proof compares algebraic and analytic Taylor expansions at a smooth point and uses injectivity of the algebraic Taylor map. The present auxiliary is the local-ring, finite-affine-coordinate formulation of that comparison. Its extension from the source chapter's locally compact fields to complete algebraically closed normed fields is explicitly part of the obligation. For the non-Archimedean geometric route see A. Chambert-Loir and F. Loeser, A non-archimedean Ax-Lindemann theorem, section 5.1, printed p.8, and the rational-point-density step in the proof of Lemma 5.3, printed p.9, https://webusers.imj-prg.fr/~francois.loeser/drinfeldv3.pdf . Regularity-to-smoothness over the algebraically closed field is Stacks Project Lemma 10.140.2, https://stacks.math.columbia.edu/tag/00TS . The statement is an auxiliary local consequence, not a verbatim statement of any of these numbered results; the analytic/algebraic germ comparison remains to be proved.

import Mathlib
set_option autoImplicit false
open Filter Topology

namespace AffineAnalytic

theorem local_mem_of_norm_vanishing_at_regular_point
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsAlgClosed K] [CharZero K] (σ : Type*) [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (a : σ → K)
    (m : MaximalSpectrum (MvPolynomial σ K))
    (hm : m.asIdeal = RingHom.ker (MvPolynomial.eval a))
    (ha : I ≤ m.asIdeal)
    (hreg : IsRegularLocalRing ((Localization.AtPrime m.asIdeal) ⧸
      I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime m.asIdeal))))
    (P : MvPolynomial σ K)
    (hP : ∀ᶠ v in 𝓝 a,
      (∀ Q ∈ I, MvPolynomial.eval v Q = 0) → MvPolynomial.eval v P = 0) :
    algebraMap (MvPolynomial σ K) (Localization.AtPrime m.asIdeal) P ∈
      I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime m.asIdeal)) := by sorry

end AffineAnalytic
