-- Prove2me | Theorems.Thm_CliffordCert_Optimal_finite_field_spread
-- name    : CliffordCert.Optimal.finite_field_spread
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:34:52.328012+00:00
-- url     : https://prove2.me/theorems/d9e6724e-b277-45af-bca6-5e0b4265dae5
-- title:
--   Lemma 6 — finite field and its binary spread
-- statement:
--   For every integer $a\ge1$, take the finite field $K=\operatorname{GF}(2^a)$. It has $2^a$ elements and binary dimension $a$. The $2^a+1$ binary subspaces
--   $$L_b=\{(x,bx):x\in K\}\quad(b\in K),\qquad L_\infty=\{(0,y):y\in K\}$$
--   cover $K^2$. Each has dimension $a$, and any two distinct members intersect exactly at zero.
--
--   This is the spread used to divide the radical without imposing a symplectic condition on its members.
--
--   Differences from the source:
--   - encoding: there is a field K of 2^a elements → the canonical Mathlib GaloisField 2 a, with its cardinality and binary dimension stated; reason: choosing a concrete witness retains the existential claim
--   - encoding: finite slopes b and the infinite slope → Option K, with none the vertical line; reason: the extra index is exactly the one point at infinity
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 12, Lemma 6, Eq. (21) (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_symplectic
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_field_spread (a : ℕ) (ha : 1 ≤ a) :
    Nat.card (SpreadField a) = 2^a ∧
    Module.finrank F₂ (SpreadField a) = a ∧
    Nat.card (Option (SpreadField a)) = 2^a+1 ∧
    (∀ z : SpreadField a × SpreadField a, ∃ b, z ∈ spreadLine a b) ∧
    (∀ b, Module.finrank F₂ (spreadLine a b) = a) ∧
    (∀ b c, b ≠ c → spreadLine a b ⊓ spreadLine a c = ⊥) := by sorry
end CliffordCert.Optimal
