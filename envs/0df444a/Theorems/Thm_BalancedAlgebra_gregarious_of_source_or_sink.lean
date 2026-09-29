-- Prove2me | Theorems.Thm_BalancedAlgebra_gregarious_of_source_or_sink
-- name    : BalancedAlgebra.gregarious_of_source_or_sink
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:15:58.884045+00:00
-- url     : https://prove2.me/theorems/246a3534-1a32-4bcd-b2b0-993ae6cb2156
-- title:
--   Sinks and sources are gregarious
-- statement:
--   Call $b$ **gregarious** when, for all $a$ and $c$ such that $a\cdot b$ and $b\cdot c$ are both defined, at least one of $(ab)c$, $a(bc)$ is defined. A left unit $u$ is a **source** when $a\cdot u$ is defined only for $a=u$, and a right unit $v$ is a **sink** when $v\cdot b$ is defined only for $b=v$.
--
--   $$x \text{ a source or a sink}\ \Longrightarrow\ x \text{ is gregarious.}$$
--
--   The manuscript records this for an arbitrary algebra: no balance and no associativity is used. The two verifications are the ones given in §4.2 — for a source, the left factor is forced to be $u$ itself, and for a sink the right factor is forced to be $v$ itself, and in both cases the product $(x\cdot y)\cdot z$ collapses to one already known to be defined.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §4.2 (p. 6): "In summary, sinks and sources are gregarious, in any algebra."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem gregarious_of_source_or_sink {A : Type*} (P : PartialAlgebra A) (x : A)
    (hx : P.IsSource x ∨ P.IsSink x) : P.Gregarious x := by sorry

end BalancedAlgebra
