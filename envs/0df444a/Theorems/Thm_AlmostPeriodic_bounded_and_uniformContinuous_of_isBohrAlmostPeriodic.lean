-- Prove2me | Theorems.Thm_AlmostPeriodic_bounded_and_uniformContinuous_of_isBohrAlmostPeriodic
-- name    : AlmostPeriodic.bounded_and_uniformContinuous_of_isBohrAlmostPeriodic
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:35:41.517434+00:00
-- url     : https://prove2.me/theorems/3eeb5b25-fe0b-4b89-bfad-053b09afb2f5
-- title:
--   Bohr almost periodic functions are bounded and uniformly continuous
-- statement:
--   **Almost periodic functions are bounded and uniformly continuous (Bohr).** Let $E$ be a normed group and let $f:\mathbb R\to E$ be almost periodic in the sense of Bohr: $f$ is continuous and for every $\varepsilon>0$ the set of $\tau\in\mathbb R$ with $\sup_{x\in\mathbb R}\|f(x+\tau)-f(x)\|\le\varepsilon$ is relatively dense. Then
--
--   1. $f$ is bounded: there is $C$ with $\|f(x)\|\le C$ for all $x\in\mathbb R$;
--   2. $f$ is uniformly continuous on $\mathbb R$.
--
--   These are the first two facts of Bohr's theory; they are used constantly, e.g. to show that the almost periodic functions form a closed subalgebra of the bounded continuous functions and to define their mean values. Masullo recalls Bohr's theory in §7.1.1 as background for strong recurrence.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 312, §7.1.1 (Bohr's theory of almost periodic functions, recalled); classical reference: H. Bohr, Zur Theorie der fastperiodischen Funktionen I, II, III, Acta Math. 45 (1924), 46 (1925), 47 (1926) [Bohr1, Bohr2, Bohr3], and H. Bohr, Almost Periodic Functions, Chelsea Publishing Company, New York, 1947 (dated 1933 in the paper's bibliography) [Bohr4], cited by the paper at this spot.

import Mathlib
import Definitions.Def_AlmostPeriodic_BohrAlmostPeriodic

open Filter Topology

set_option autoImplicit false

namespace AlmostPeriodic

theorem bounded_and_uniformContinuous_of_isBohrAlmostPeriodic
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hf : IsBohrAlmostPeriodic f) :
    (∃ C : ℝ, ∀ x : ℝ, ‖f x‖ ≤ C) ∧ UniformContinuous f := by sorry

end AlmostPeriodic
