-- Prove2me | Theorems.Thm_AlmostPeriodic_parseval_of_isBohrAlmostPeriodic
-- name    : AlmostPeriodic.parseval_of_isBohrAlmostPeriodic
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T18:35:34.906479+00:00
-- url     : https://prove2.me/theorems/1f0146b1-2210-427b-8616-234a1e2ddbc2
-- title:
--   Parseval's identity for Bohr almost periodic functions: $\sum_{\lambda}|a(\lambda)|^2=M(|f|^2)$
-- statement:
--   **Parseval's identity for almost periodic functions (Bohr).** Let $f:\mathbb R\to\mathbb C$ be almost periodic in the sense of Bohr. Then:
--
--   1. for every frequency $\lambda\in\mathbb R$ the Bohr–Fourier coefficient
--   $$a(\lambda)=\lim_{T\to+\infty}\frac1T\int_0^T f(x)\,e^{-i\lambda x}\,dx$$
--   exists;
--   2. the mean value $M(|f|^2)=\lim_{T\to+\infty}\frac1T\int_0^T|f(x)|^2\,dx$ exists;
--   3. Parseval's identity holds:
--   $$\sum_{\lambda\in\mathbb R}|a(\lambda)|^2=M(|f|^2),$$
--   as an (unconditionally convergent) sum of non-negative terms over all real $\lambda$.
--
--   In particular $a(\lambda)\neq0$ for at most countably many $\lambda$ (the Bohr spectrum of $f$ is countable), and an almost periodic function all of whose Bohr–Fourier coefficients vanish satisfies $M(|f|^2)=0$. Parseval's identity is the central theorem of Bohr's theory (equivalent to the uniqueness and approximation theorems); Masullo's §7.1.1 recalls this theory as the motivation for strong recurrence.
--
--   **Formalization Note.** The coefficients and the mean are asserted to exist as limits of $T^{-1}\int_0^T$ (for almost periodic functions the limit of $T^{-1}\int_a^{a+T}$ is the same, uniformly in $a$). The sum is Mathlib's unconditional `HasSum` over the index type $\mathbb R$; summability of a non-negative family over $\mathbb R$ forces countable support.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 312, §7.1.1 (Bohr's theory of almost periodic functions, recalled); classical reference: H. Bohr, Zur Theorie der fastperiodischen Funktionen I, II, III, Acta Math. 45 (1924), 46 (1925), 47 (1926) [Bohr1, Bohr2, Bohr3], and H. Bohr, Almost Periodic Functions, Chelsea Publishing Company, New York, 1947 (dated 1933 in the paper's bibliography) [Bohr4], cited by the paper at this spot.

import Mathlib
import Definitions.Def_AlmostPeriodic_BohrAlmostPeriodic

open Filter Topology

set_option autoImplicit false

namespace AlmostPeriodic

theorem parseval_of_isBohrAlmostPeriodic (f : ℝ → ℂ) (hf : IsBohrAlmostPeriodic f) :
    ∃ (c : ℝ → ℂ) (M : ℝ),
      (∀ ξ : ℝ, Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
          ∫ x in (0 : ℝ)..T, f x * Complex.exp (-((ξ * x : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 (c ξ))) ∧
      Tendsto (fun T : ℝ => T⁻¹ * ∫ x in (0 : ℝ)..T, ‖f x‖ ^ 2) atTop (𝓝 M) ∧
      HasSum (fun ξ : ℝ => ‖c ξ‖ ^ 2) M := by sorry

end AlmostPeriodic
