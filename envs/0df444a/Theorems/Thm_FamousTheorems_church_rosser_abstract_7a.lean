-- Prove2me | Theorems.Thm_FamousTheorems_church_rosser_abstract_7a
-- name    : FamousTheorems.church_rosser_abstract_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:37.938727+00:00
-- url     : https://prove2.me/theorems/c68d21f8-93d7-4e24-9b13-31405bbd12f8
-- title:
--   Abstract Church–Rosser lemma (strip lemma for relations)
-- statement:
--   **Abstract Church–Rosser lemma.** Let $r$ be a binary relation on a set $\alpha$, with reflexive-transitive closure $r^*$ and reflexive closure $r^=$. Suppose that whenever $a\,r\,b$ and $a\,r\,c$ there is $d$ with $b\,r^=\,d$ and $c\,r^*\,d$. Then $r^*$ is confluent: if $a\,r^*\,b$ and $a\,r^*\,c$, there is $d$ with $b\,r^*\,d$ and $c\,r^*\,d$.
--
--   This is the diagram-chasing lemma behind the Church–Rosser theorem of Church and Rosser (1936) for the $\lambda$-calculus. It reduces confluence of a rewriting system to a one-step condition. Confluence implies that normal forms are unique when they exist, which is basic in term rewriting and the semantics of programming languages.
--
--   **Formalization note.** Mathlib's `Relation.church_rosser`. `Relation.ReflGen r` and `Relation.ReflTransGen r` are the reflexive and reflexive-transitive closures of $r$. `Relation.Join R b c` means that there is $d$ with $R\,b\,d$ and $R\,c\,d$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Relation.church_rosser`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem church_rosser_abstract_7a {α : Type*} {r : α → α → Prop} {a b c : α}
    (h : ∀ a b c, r a b → r a c → ∃ d, Relation.ReflGen r b d ∧ Relation.ReflTransGen r c d)
    (hab : Relation.ReflTransGen r a b) (hac : Relation.ReflTransGen r a c) :
    Relation.Join (Relation.ReflTransGen r) b c := by sorry

end FamousTheorems
