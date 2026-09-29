-- Prove2me | Theorems.Thm_Farey_pairs_inj
-- name    : Farey.pairs_inj
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-10T10:47:57.992704+00:00
-- url     : https://prove2.me/theorems/0775d64c-2c08-4307-a3eb-723a56865170
-- title:
--   Distinct Farey pairs represent distinct fractions
-- statement:
--   If two Farey pairs of order $P$ represent the same real number, they are the same pair:
--
--   $$\frac{a}{q} = \frac{a'}{q'} \;\Longrightarrow\; (q,a) = (q',a').$$
--
--   Equivalently, the map $(q,a) \mapsto a/q$ is injective on the dissection. This is exactly what makes the major arcs well defined: each arc is centred at a distinct rational, so distinct pairs give distinct centres and the arcs can be indexed by the pairs themselves. It rests on coprimality — without $\gcd(a,q)=1$ the fraction $2/4$ would duplicate $1/2$.
-- source:
--   Standard Farey-dissection facts. See R. C. Vaughan, The Hardy-Littlewood Method, 2nd ed., Cambridge University Press 1997, Chapter 2; Hardy & Wright, An Introduction to the Theory of Numbers, Chapter III.

import Definitions.Def_Farey
import Mathlib

namespace Farey

theorem pairs_inj {P : ℕ} {p p' : ℕ × ℕ} (hp : p ∈ pairs P) (hp' : p' ∈ pairs P)
    (h : (p.2 : ℝ) / (p.1 : ℝ) = (p'.2 : ℝ) / (p'.1 : ℝ)) : p = p' := by
  sorry

end Farey
