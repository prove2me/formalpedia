-- Prove2me | Theorems.Thm_DiazModulus_diaz_on_axes_of_hermite_lindemann
-- name    : DiazModulus.diaz_on_axes_of_hermite_lindemann
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T06:45:29.529851+00:00
-- url     : https://prove2.me/theorems/36d1a5d8-6cb7-4a84-baec-03e375793e25
-- title:
--   Diaz's conjecture on the real and imaginary axes, given Hermite--Lindemann
-- statement:
--   **Conditional on Hermite--Lindemann**, which is taken as an explicit hypothesis, Diaz's conjecture holds for $u$ on either coordinate axis.
--
--   If $u \neq 0$ is real then $u = \pm|u|$; if $u$ is purely imaginary then $u = \pm i|u|$. Either way, algebraicity of $|u|$ forces $u$ itself to be algebraic (using that $i$ is algebraic), and Hermite--Lindemann then gives that $e^{u}$ is transcendental.
--
--   Two honest remarks about what this milestone is and is not.
--
--   It is *conditional*: the hypothesis `HermiteLindemann` is supplied as an argument, which is why the name says so. The mission discharges that hypothesis separately in `DiazModulus.hermite_lindemann_holds`.
--
--   And on the axes the "algebraic modulus" hypothesis — the distinctive feature of Diaz's question, which is about $|u|$ rather than about $u$ — collapses to plain algebraicity of $u$. So the conclusion here is an instance of the assumed Hermite--Lindemann statement, not a claim about moduli. The content is the case analysis, not the transcendence.
--
--   The milestone earns its place for a reason visible only from `DiazModulus.diaz_of_schanuel`: the axes are exactly the locus where $u$ and $\bar u$ fail to be linearly independent over $\mathbb{Q}$. Writing $\bar u = qu$ with $q$ rational and $|\bar u| = |u|$ forces $q = \pm 1$, hence $u$ real or purely imaginary. This is precisely the degenerate branch that any Schanuel- or Baker-style argument must dispose of separately, and the one branch where the answer is elementary.
-- source:
--   G. Diaz, Utilisation de la conjugaison complexe dans l'etude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Theor. Nombres Bordeaux 16 (2004), no. 3, 535-553, doi:10.5802/jtnb.459, section 5.1, p. 550

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_on_axes_of_hermite_lindemann (hHL : HermiteLindemann) (u : ℂ) (hu : u ≠ 0)
    (hax : u.im = 0 ∨ u.re = 0) (hmod : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ)) :
    Transcendental ℚ (Complex.exp u) := by sorry
end DiazModulus
