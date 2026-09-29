-- Prove2me | Theorems.Thm_Diaz_fibre_second_point_is_conj
-- name    : Diaz.fibre_second_point_is_conj
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T10:56:53.680537+00:00
-- url     : https://prove2.me/theorems/227f7a24-ed09-4b1f-b1be-bb8322575a59
-- title:
--   On the torsion branch the second point of a fibre is the conjugate and the common value is real
-- statement:
--   **Statement.** Let $\Im u = k\pi$ with $k\in\mathbb{Z}\setminus\{0\}$ and
--   $\lVert u\rVert^{2}\in\bar{\mathbb{Q}}$; let $q\in\mathbb{Q}$, and let
--   $n\in\mathbb{Z}\setminus\{0\}$ be such that the translate $qu+2\pi n i$ again has algebraic
--   modulus. Then
--
--   1. $qk=-n$;
--   2. $qu+2\pi n i=\overline{qu}$ --- the translate **is** the conjugate;
--   3. $e^{qu}$ is real.
--
--   So at every point of the rational orbit of a torsion-branch candidate, the only non-trivial period
--   translate that stays on the locus is the conjugate, and the exponential value shared by the two
--   points is real.
--
--   **Source and attribution.** All the mathematics of this node is Carlo Perassi's, and it is unpublished apart from this node. **No novelty is claimed.** This is the last clause of his theorem on
--   rational-translate rigidity: "$\nu=0$ if and only if
--   $\theta\in\pi\mathbb{Q}$, in which case $r_{0}=-\theta/\pi$ and $u+2\pi ir_{0}=\bar u$;
--   hence in the torsion branch the second candidate is $\bar u$." Of that theorem only the counting
--   half --- at most one non-zero rational translate --- had been published, as
--   `Diaz.q_translate_unique`. Nothing here is new.
--
--   **What it settles on this branch.** Three published nodes have their hypotheses fixed by it.
--   `Diaz.fibre_at_most_two` and its engine `Diaz.second_difference_mem` are *saturated* by the
--   trivial pair $\{v,\bar v\}$, which carries no relation. `Diaz.q_translate_unique` is saturated
--   the same way, with $r_{0}=-qk$. And `Diaz.nonreal_two_point_fibre_pi_sq` --- whose conclusion,
--   $\pi^{2}\notin\tilde{\mathcal{L}}$, is the strongest on offer --- requires the common value
--   $\alpha=e^{v}$ to be **non-real**; clause 3 says that hypothesis has no instance anywhere on the
--   rational orbit of a torsion-branch candidate. That is the exact difference between this branch and
--   the configurations where the $e^{\pi^{2}}$ route fires.
--
--   **Proof.** Apply `Diaz.period_plane_classification` with $(a,b,c)=(q,0,n)$. The second alternative
--   would give $n=0$; so the first holds, $n=-qk$, and substituting
--   $u-\bar u=2ik\pi$ turns $qu+2\pi ni$ into $q\bar u=\overline{qu}$. For clause 3,
--   $\Im(qu)=qk\pi=-n\pi\in\pi\mathbb{Z}$, and $\Im e^{w}=e^{\Re w}\sin(\Im w)$ vanishes
--   there.

import Mathlib

open ComplexConjugate

theorem Diaz.fibre_second_point_is_conj {u : ℂ} {k : ℤ} (hk : k ≠ 0)
    (him : u.im = (k : ℝ) * Real.pi)
    (hn : IsAlgebraic ℚ ((Complex.normSq u : ℝ) : ℂ)) (q : ℚ) (n : ℤ) (hn0 : n ≠ 0)
    (halg : IsAlgebraic ℚ ((Complex.normSq ((q : ℂ) * u
        + 2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) : ℝ) : ℂ)) :
    q * (k : ℚ) = -(n : ℚ)
      ∧ (q : ℂ) * u + 2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I = conj ((q : ℂ) * u)
      ∧ (Complex.exp ((q : ℂ) * u)).im = 0 := by sorry
