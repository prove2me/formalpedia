-- Prove2me | Theorems.Thm_AlmostPeriodic_isBohrAlmostPeriodic_closed_subalgebra
-- name    : AlmostPeriodic.isBohrAlmostPeriodic_closed_subalgebra
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:35:31.727899+00:00
-- url     : https://prove2.me/theorems/8a601735-f628-4403-b3ef-effbb441bd95
-- title:
--   Bohr almost periodic functions form a uniformly closed algebra: constants, sums, products and uniform limits
-- statement:
--   **The Bohr almost periodic functions form a uniformly closed subalgebra (Bohr).** Let $R$ be a normed ring (for instance $\mathbb C$). For functions $\mathbb R\to R$:
--
--   1. every constant function is almost periodic;
--   2. if $f$ and $g$ are almost periodic, so is $f+g$;
--   3. if $f$ and $g$ are almost periodic, so is $fg$;
--   4. if $F_n$ are almost periodic and $F_n\to f$ uniformly on $\mathbb R$, then $f$ is almost periodic.
--
--   Part 2 is Bohr's theorem on sums. For $R=\mathbb C$, together with boundedness and uniform continuity, the theorem says that the almost periodic functions form a uniformly closed subalgebra of the Banach algebra $C_b(\mathbb R)$ of bounded continuous functions with the sup norm (for a general normed ring $R$, a uniformly closed subring of the bounded continuous $R$-valued functions). Since continuous periodic functions are almost periodic, finite sums and products of continuous periodic functions with arbitrary periods are almost periodic; this is the real-variable counterpart of the example in Masullo §7.1.1 (p. 312), which concerns vertically periodic holomorphic functions on vertical strips.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 312, §7.1.1 (finite sums and finite products of periodic functions with different periods are almost periodic); classical reference: H. Bohr, Zur Theorie der fastperiodischen Funktionen I, II, III, Acta Math. 45 (1924), 46 (1925), 47 (1926) [Bohr1, Bohr2, Bohr3], and H. Bohr, Almost Periodic Functions, Chelsea Publishing Company, New York, 1947 [Bohr4] (dated 1933 in the paper's bibliography), cited by the paper in §7.1.1 (pp. 312–313).

import Mathlib
import Definitions.Def_AlmostPeriodic_BohrAlmostPeriodic

open Filter Topology

set_option autoImplicit false

namespace AlmostPeriodic

theorem isBohrAlmostPeriodic_closed_subalgebra {R : Type*} [NormedRing R] :
    (∀ c : R, IsBohrAlmostPeriodic (fun _ : ℝ => c)) ∧
    (∀ f g : ℝ → R, IsBohrAlmostPeriodic f → IsBohrAlmostPeriodic g →
      IsBohrAlmostPeriodic (fun x => f x + g x)) ∧
    (∀ f g : ℝ → R, IsBohrAlmostPeriodic f → IsBohrAlmostPeriodic g →
      IsBohrAlmostPeriodic (fun x => f x * g x)) ∧
    (∀ (F : ℕ → ℝ → R) (f : ℝ → R), (∀ n : ℕ, IsBohrAlmostPeriodic (F n)) →
      TendstoUniformly F f atTop → IsBohrAlmostPeriodic f) := by sorry

end AlmostPeriodic
