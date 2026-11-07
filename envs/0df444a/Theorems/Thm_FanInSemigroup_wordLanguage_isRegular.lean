-- Prove2me | Theorems.Thm_FanInSemigroup_wordLanguage_isRegular
-- name    : FanInSemigroup.wordLanguage_isRegular
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:28.42669+00:00
-- url     : https://prove2.me/theorems/494ea155-2d21-4ecd-bbb5-cf9b937ea73c
-- title:
--   pp.54–55 — $L(S,a)$ is regular
-- statement:
--   For every finite semigroup $S$ and every $a\in S$, the language $L(S,a)$ of nonempty words over $S$ with product $a$ is regular.
--
--   This puts the semigroup's product into the setting of regular sets, in which the rest of the upper bound takes place.
--
--   Differences from the source:
--   - encoding: the alphabet S^Σ, a copy of S → the alphabet S; reason: a renaming of the letters
--   - encoding: "regular" → Language.IsRegular, Mathlib's existence of a finite deterministic automaton; reason: the standard definition
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, §2, pp.54–55 (unnumbered)

import Definitions.Def_FanInSemigroup_wordLanguage

set_option autoImplicit false

namespace FanInSemigroup

/-- **L(S,a) is regular.** Chandra, Fortune, Lipton, STOC 1983, pp.54–55 (unnumbered): "As a
consequence, for any a in the semigroup, the set {w^Σ ∈ (S^Σ)* : w = a in the semigroup} is
regular. This set is denoted L(S,a)." -/
theorem wordLanguage_isRegular {S : Type*} [Semigroup S] [Finite S] (a : S) :
    (wordLanguage a).IsRegular := by sorry

end FanInSemigroup
