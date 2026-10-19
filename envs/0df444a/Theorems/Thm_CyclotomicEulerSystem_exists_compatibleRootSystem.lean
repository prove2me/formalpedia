-- Prove2me | Theorems.Thm_CyclotomicEulerSystem_exists_compatibleRootSystem
-- name    : CyclotomicEulerSystem.exists_compatibleRootSystem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T15:27:04.253989+00:00
-- url     : https://prove2.me/theorems/8b4ae9b2-802b-45c0-bbef-bd4eaa9287d2
-- title:
--   Existence of a compatible system of roots of unity
-- statement:
--   A compatible system of roots of unity exists: there is a function $n\mapsto\zeta_n\in\mathbb C$ such that
--
--   1. for every square-free positive integer $n$, $\zeta_n$ is a primitive $n$-th root of unity, and
--   2. $\zeta_{mn}=\zeta_m\zeta_n$ for all coprime square-free positive integers $m,n$.
--
--   $$\exists\,\zeta:\mathbb N\to\mathbb C\ \text{ compatible.}$$
--
--   This is the "pick" step of the source's construction: it shows the hypotheses of the norm and congruence relations can be met, so those statements are not vacuous.
-- source:
--   Wikipedia, "Euler system", revision 1353502478 (https://en.wikipedia.org/w/index.php?title=Euler_system&oldid=1353502478), section "Examples / Cyclotomic units", displayed relations (norm relation and congruence relation) and the preceding sentence "For every square-free positive integer n pick an n-th root ζ_n of 1, with ζ_mn = ζ_m ζ_n for m,n coprime. Then the cyclotomic Euler system is the set of numbers α_n = 1 − ζ_n."

import Mathlib
import Definitions.Def_CyclotomicEulerSystem_defs

open NumberField

namespace CyclotomicEulerSystem

theorem exists_compatibleRootSystem : ∃ ζ : ℕ → ℂ, IsCompatibleRootSystem ζ := by sorry

end CyclotomicEulerSystem
