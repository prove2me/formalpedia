-- Prove2me | Theorems.Thm_CelestialHolography_lorentz_acts_as_mobius
-- name    : CelestialHolography.lorentz_acts_as_mobius
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T02:31:18.956865+00:00
-- url     : https://prove2.me/theorems/199673ff-a212-48f0-86aa-34a53624a0a6
-- title:
--   Lorentz transformations act on the celestial sphere as Möbius transformations
-- statement:
--   **Goal (§2.2 eq. (3), §3.1 eq. (11)).** Let $M=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in SL(2,\mathbb C)$ and let $\Lambda(M)x=V(M\,H(x)\,M^\dagger)$ be the induced map of Minkowski space $\mathbb R^{1,3}$. Then
--
--   1. $\Lambda(M)$ is a Lorentz transformation: $\|\Lambda(M)x\|_\eta^2=\|x\|_\eta^2$ for all $x\in\mathbb R^4$;
--   2. on the celestial null vectors $q(z)$ of eq. (11) it acts by the Möbius transformation of eq. (3): for every $z\in\mathbb C$ with $cz+d\neq0$,
--   $$\Lambda(M)\,q(z)=|cz+d|^2\;q\!\left(\frac{az+b}{cz+d}\right).$$
--
--   So a Lorentz transformation maps the null direction labelled by $z$ to the one labelled by $z'=(az+b)/(cz+d)$, and rescales the energy $\omega$ in $p=\omega q(z)$ by the positive factor $|cz+d|^2$ — the factor behind the primary transformation law (13) of celestial operators.
-- source:
--   F. Barzi, *Celestial Holography, A Hitchhiker's Guide to the Celestial Sphere*, arXiv:2608.07568v1 [hep-th], https://arxiv.org/abs/2608.07568, §2.2 eq. (3) and §3.1 eq. (11)

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

namespace CelestialHolography

theorem lorentz_acts_as_mobius (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (∀ x : Fin 4 → ℝ, minkowskiNormSq (lorentzOfSL2C M x) = minkowskiNormSq x) ∧
    ∀ z : ℂ, M 1 0 * z + M 1 1 ≠ 0 →
      lorentzOfSL2C M (nullVector z) =
        Complex.normSq (M 1 0 * z + M 1 1) • nullVector (mobius M z) := by sorry

end CelestialHolography
