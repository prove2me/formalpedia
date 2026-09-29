-- Prove2me | Theorems.Thm_DiazModulus_nongeneric_rational_modulus_orbit
-- name    : DiazModulus.nongeneric_rational_modulus_orbit
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T06:25:48.943002+00:00
-- url     : https://prove2.me/theorems/f22d3ed4-1827-4b5f-8ec8-cdecb9e3147a
-- title:
--   Logarithms algebraic over ℚ(π) with rational squared modulus are rationally proportional, up to conjugation
-- statement:
--   Let $u, v$ be non-zero complex numbers such that $e^{u}$ and $e^{v}$ are algebraic, $u$ and $v$ are algebraic over $\mathbb{Q}(\pi)$, and $|u|^{2} = u\bar u$ and $|v|^{2} = v\bar v$ are rational. Then there is $q \in \mathbb{Q}$ with
--
--   $$v = q\,u \qquad\text{or}\qquad v = q\,\bar u.$$
--
--   A non-zero logarithm $u$ of an algebraic number with $|u|$ algebraic would be a counterexample to Diaz's conjecture. The theorem says that the counterexamples algebraic over $\mathbb{Q}(\pi)$ with a rational squared modulus form at most one orbit under rational scaling and complex conjugation.
--
--   **Proof.** Since $v \neq 0$, the rational $|v|^{2}$ is non-zero, so $u\bar u = c\, v\bar v$ with $c = |u|^{2}/|v|^{2} \in \mathbb{Q}$. The conjugates are algebraic over $\mathbb{Q}(\pi)$ too, as $\bar u = |u|^{2}/u$ and $\bar v = |v|^{2}/v$. So $u, v, \bar u, \bar v$ generate a field of transcendence degree at most one (`Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin`), and `DiazModulus.log_pair_rigid_of_trdeg_one` gives the rational $q$.
--
--   **Novelty.** Not found in the sources read (among them Diaz 2004 and 2007, Roy–Waldschmidt 1995 and 1997, and Waldschmidt 1973, 1974 and 2005). It follows in a few lines from the four exponentials theorem in transcendence degree one (M. Waldschmidt, *Solution du huitième problème de Schneider*, J. Number Theory **5** (1973), Corollaire 4; Theorem 1 of D. Roy and M. Waldschmidt, Proc. Japan Acad. **71** (1995)), which is `DiazModulus.log_pair_rigid_of_trdeg_one` on this site. The nearest statement found has the same shape and a different content: by the Gelfond–Schneider theorem, the non-zero algebraic $\beta$ with $e^{\beta}$ algebraic form either the empty set or a single orbit $\mathbb{Q}^{\times}\beta_{0}$ (G. Diaz, J. Théor. Nombres Bordeaux **16** (2004), Théorème 5).
-- source:
--   Not found in the sources read (among them Diaz 2004 and 2007, Roy–Waldschmidt 1995 and 1997, and Waldschmidt 1973, 1974 and 2005). It follows in a few lines from the four exponentials theorem in transcendence degree one: M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Corollaire 4; recorded as Theorem 1 of D. Roy and M. Waldschmidt, Quadratic relations between logarithms of algebraic numbers, Proc. Japan Acad. Ser. A 71 (1995), 151–153, who also credit W. D. Brownawell (J. Number Theory 6, 1974). For the orbit shape compare G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Théorème 5. Statement and formal proof: Diaz modulus mission, 29 September 2026 (C. Perassi).

import Mathlib

open ComplexConjugate

namespace DiazModulus

/-- Two non-zero logarithms of algebraic numbers, algebraic over `ℚ[π]` and with rational squared
moduli, are rationally proportional up to complex conjugation. -/
theorem nongeneric_rational_modulus_orbit (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (heu : IsAlgebraic ℚ (Complex.exp u)) (hev : IsAlgebraic ℚ (Complex.exp v))
    (ru rv : ℚ) (hru : u * conj u = ru) (hrv : v * conj v = rv)
    (hua : IsAlgebraic (Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) u)
    (hva : IsAlgebraic (Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) v) :
    ∃ q : ℚ, v = (q : ℂ) * u ∨ v = (q : ℂ) * conj u := by
  sorry

end DiazModulus
