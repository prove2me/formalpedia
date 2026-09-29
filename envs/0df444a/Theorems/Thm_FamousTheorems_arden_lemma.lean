-- Prove2me | Theorems.Thm_FamousTheorems_arden_lemma
-- name    : FamousTheorems.arden_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:27:03.030237+00:00
-- url     : https://prove2.me/theorems/6dff9f7a-c700-4ac6-8965-465a61038f0e
-- title:
--   Arden's lemma
-- statement:
--   **Arden's lemma.** Let $l,m,n$ be languages over an alphabet $\alpha$ with the empty word not in $m$. Then $l$ solves the equation
--   $$l=m\,l\cup n$$
--   if and only if $l=m^*n$. So $m^*n$ is the unique solution.
--
--   It is the standard tool for solving systems of language equations. It gives the conversion of finite automata into regular expressions (Brzozowski's algebraic method) and is basic in the algebraic theory of regular languages.
--
--   **Formalization note.** Mathlib's `Language.self_eq_mul_add_iff`. In `Language α`, `+` is union, `*` is concatenation, and `KStar.kstar m` is the Kleene star $m^*$. The hypothesis `[] ∉ m` excludes the empty word.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Language.self_eq_mul_add_iff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem arden_lemma {α : Type*} {l m n : Language α} (hm : [] ∉ m) : l = m * l + n ↔ l = KStar.kstar m * n := by sorry

end FamousTheorems
