-- Prove2me | Theorems.Thm_FiniteTableVerification_sparse_default_iff
-- name    : FiniteTableVerification.sparse_default_iff
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T20:45:04.731078+00:00
-- url     : https://prove2.me/theorems/4d04b3f4-6f7a-5eba-929a-6cd0e29b3bed
-- title:
--   Exact verification of a finite transition table with a default action
-- statement:
--   Keys are partitioned into groups, each with a finite set of admissible keys. A table supplies explicit actions on a finite set of keys and a fixed fallback on unlisted keys. A finite set of groups contains every group for which the fallback fails the local action rule. Every admissible key satisfies its group's rule exactly when every listed admissible key passes its local check and each group with an invalid fallback has as many distinct admissible listed keys as admissible keys in total.
-- source:
--   An elementary consequence of finite-set inclusion and cardinality, motivated by sparse transition-table verification.

import Mathlib

theorem FiniteTableVerification.sparse_default_iff {Key Group Action : Type*}
    [DecidableEq Key] (groupOf : Key → Group) (admissible : Group → Finset Key)
    (listed : Finset Key) (groups : Finset Group) (action : Key → Action) (fallback : Action)
    (valid : Group → Action → Prop)
    (group_consistent : ∀ g k, k ∈ admissible g → groupOf k = g)
    (unlisted_default : ∀ k, k ∉ listed → action k = fallback)
    (unlisted_groups_valid : ∀ g, g ∉ groups → valid g fallback) :
    (∀ k, k ∈ admissible (groupOf k) → valid (groupOf k) (action k)) ↔
      (∀ k ∈ listed, k ∈ admissible (groupOf k) → valid (groupOf k) (action k)) ∧
      (∀ g ∈ groups, ¬ valid g fallback →
        (admissible g ∩ listed).card = (admissible g).card) := by sorry
