-- Prove2me | Theorems.Thm_AlmostPeriodic_upperDensity_pos_of_isAlmostPeriodicOnStrip
-- name    : AlmostPeriodic.upperDensity_pos_of_isAlmostPeriodicOnStrip
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:36:01.556085+00:00
-- url     : https://prove2.me/theorems/6b929380-d2e5-4d81-95a9-8cf6f0a75c07
-- title:
--   Almost periodic analytic functions on a vertical strip are strongly recurrent (Bagchi)
-- statement:
--   **Almost periodicity implies strong recurrence.** Let $f$ be an almost periodic analytic function on the open vertical strip $\mathbf C_{(a,b)}$ (holomorphic there and almost periodic in the sense of Bohr, uniformly on every closed substrip). Then $f$ is *strongly recurrent* on $\mathbf C_{(a,b)}$ in the sense of Bagchi: for every compact set $K\subset\mathbf C_{(a,b)}$ and every $\varepsilon>0$ the set
--   $$A(K,\varepsilon)=\Big\{t\in\mathbb R:\ \sup_{s\in K}|f(s+it)-f(s)|<\varepsilon\Big\}$$
--   has positive upper density
--   $$\bar d(A)=\limsup_{T\to+\infty}\frac{\lambda(A\cap[-T,T])}{2T}>0,$$
--   where $\lambda$ is Lebesgue measure.
--
--   This is the comparison made in Masullo §7.1.1 (p. 313): strong recurrence "is indeed weaker than almost periodicity (for analytic functions on vertical strips of bounded width)". The paper cites Bohr for analytic almost periodic functions and Bagchi's thesis for strong recurrence; strong recurrence is then the notion used in Lemma 7.1.1.1 and Proposition B.5.3.3.
--
--   **Formalization Note.** The upper density is the platform's `MasulloGRH.upperDensity` (Definition B.5.3.1(1)), and the supremum over $K$ is written `sSup` of the image of $K$. For $K=\varnothing$ the Lean supremum is $0$ and the set is all of $\mathbb R$, so this degenerate case holds as well. The paper's definition on p. 314 uses an open interval containing $0$; the implication holds for every open interval $(a,b)$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 313, §7.1.1 (strong recurrence is weaker than almost periodicity for analytic functions on vertical strips; definition of strong recurrence p. 314 and Definition B.5.3.1); classical reference: H. Bohr, Almost Periodic Functions, Chelsea Publishing Company, New York, 1947 (dated 1933 in the paper's bibliography), Appendix II, §104, p. 101 and §106, p. 104 [Bohr4], and B. Bagchi, The statistical behavior and universality properties of the Riemann Zeta Function and other allied Dirichlet series, PhD Thesis, Indian Statistical Institute, 1981, Ch. 2, §2.4, Def. 2.4.1 and Prop. 2.4.2, p. 46 [Ba1], as cited by the paper on p. 313.

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm
import Definitions.Def_AlmostPeriodic_AnalyticStrip

open Filter Topology

set_option autoImplicit false

namespace AlmostPeriodic

theorem upperDensity_pos_of_isAlmostPeriodicOnStrip
    (f : ℂ → ℂ) (a b : ℝ) (hf : IsAlmostPeriodicOnStrip f a b)
    (K : Set ℂ) (hK : IsCompact K) (hKs : K ⊆ {s : ℂ | a < s.re ∧ s.re < b})
    (ε : ℝ) (hε : 0 < ε) :
    0 < MasulloGRH.upperDensity
      {t : ℝ | sSup ((fun s : ℂ => ‖f (s + (t : ℂ) * Complex.I) - f s‖) '' K) < ε} := by sorry

end AlmostPeriodic
