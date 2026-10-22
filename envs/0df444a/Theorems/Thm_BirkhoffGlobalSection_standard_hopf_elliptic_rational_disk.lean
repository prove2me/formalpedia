-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_standard_hopf_elliptic_rational_disk
-- name    : BirkhoffGlobalSection.standard_hopf_elliptic_rational_disk
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T04:54:54.733101+00:00
-- url     : https://prove2.me/theorems/16655647-3fc9-4f21-98de-684d337badcd
-- title:
--   The standard Hopf circle bounds a positive elliptic rational disk
-- statement:
--   The positive standard Hopf circle in the standard contact sphere bounds a lifted rational two-disk with exactly one positive elliptic characteristic singularity:
--
--   $$H(S^1)=\partial D,\qquad H(x,y)=(x,0,-y,0).$$
--
--   The disk is smooth, embedded and immersed, has positively transverse boundary, and its only antipodal coincidences are opposite boundary points. Its characteristic field has a unique zero, placed at the parameter origin, with positive scalar linearization. This supplies a concrete reference disk for comparison with geometric retrograde bindings.
-- source:
--   Explicit stereographic hemisphere parametrization f(x,y)=(2x,1-x^2-y^2,-2y,0)/(1+x^2+y^2). Direct coordinate consequence of Def_BirkhoffGlobalSection_EllipticRationalDisk; its pullback radial contact form is 2(x dy-y dx)/(1+x^2+y^2)^2, so DW(0)=2 id. Contact sign convention: Def_BirkhoffGlobalSection_TransverseHopf.

import Definitions.Def_BirkhoffGlobalSection_EllipticRationalDisk
open scoped ContDiff

namespace BirkhoffGlobalSection

theorem standard_hopf_elliptic_rational_disk :
    Nonempty (PositiveEllipticRationalDisk (standardHopfCircle '' unitCircle)) := by sorry

end BirkhoffGlobalSection
