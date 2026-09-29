-- Prove2me | Theorems.Thm_DiazModulus_candidate_one_log_saturation
-- name    : DiazModulus.candidate_one_log_saturation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-12T09:44:46.284561+00:00
-- url     : https://prove2.me/theorems/cf5024d1-43b6-47ac-b3dd-5298beba22a4
-- title:
--   A candidate in $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}\ell$ is a rational multiple of $\ell$; no candidate is $a + b\pi$
-- statement:
--   **A counterexample meets no algebraic line through a single logarithm, and in particular is not of the form $a + b\pi$.**
--
--   Write $\overline{\mathbb{Q}}$ for the algebraic numbers and $\mathcal{L} = \{z : e^{z} \in \overline{\mathbb{Q}}\}$. A **candidate** is a $u$ with $u \neq 0$, $|u|$ algebraic and $e^{u}$ algebraic, i.e. a counterexample to Diaz's modulus conjecture.
--
--   Assume **Baker's theorem** in the inhomogeneous two-logarithm form carried here as `hB` (a non-zero $\overline{\mathbb{Q}}$-linear combination of two $\mathbb{Q}$-linearly independent elements of $\mathcal{L}$ is transcendental) and Hermite--Lindemann. Then for every candidate $u$:
--
--   $$u \in \overline{\mathbb{Q}} + \overline{\mathbb{Q}}\,\ell \ \text{ for some } \ell \in \mathcal{L} \quad\Longrightarrow\quad u \in \mathbb{Q}\,\ell ,$$
--
--   and consequently
--
--   $$u \neq a + b\pi \qquad \text{for all } a, b \in \overline{\mathbb{Q}} .$$
--
--   **Mathematical role.** The first clause is the one-logarithm case of Baker saturation: inside an algebraic affine line spanned by a single logarithm, the only elements of $\mathcal{L}$ are the *rational* multiples of that logarithm. The algebraic span collapses to the rational one, which is why no genuinely new logarithm can be manufactured from one old one by algebraic coefficients.
--
--   The second clause is the instance $\ell = i\pi$, and it is the reason the plane $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}\pi$ is closed off: saturation forces $u$ to be a rational multiple of $i\pi$, whence $|u| \in \mathbb{Q}_{>0}\,\pi$ is transcendental, contradicting the candidate's algebraic modulus. So the shape of a counterexample cannot be as simple as an algebraic combination of $1$ and $\pi$, and by the same mechanism it cannot be an algebraic combination of $1$ and any one logarithm of an algebraic number.
--
--   The boundary of the statement is worth recording: it does **not** extend to two logarithms at once. An algebraic combination of $\log 2$ and $i\pi$ — the point $\log 2 + i\pi$, a logarithm of $-2$ — is not excluded by this argument, and is the standing open test case for the conjecture.
-- source:
--   Baker's theorem in the inhomogeneous form (A. Baker, Linear forms in the logarithms of algebraic numbers I-IV, Mathematika 1966-1968), carried as an explicit hypothesis. The saturation consequence and its application to a hypothetical counterexample of Diaz's modulus conjecture are from C. Perassi's working notes of 12 September 2026, developed alongside this mission.

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem candidate_one_log_saturation
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y))
    (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u) :
    (∀ l : ℂ, l ∈ LogAlg → ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar →
        u = a + b * l → ∃ r : ℚ, u = (r : ℂ) * l)
      ∧ (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → u ≠ a + b * ((Real.pi : ℝ) : ℂ)) := by sorry
end DiazModulus
