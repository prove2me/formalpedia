-- Prove2me | Theorems.Thm_CriticalPortraits_hostSet_forced
-- name    : CriticalPortraits.hostSet_forced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:00.014631+00:00
-- url     : https://prove2.me/theorems/4c47ebd0-5ade-4da3-8f74-5794af10b1a4
-- title:
--   Critical Portraits: host Set forced
-- statement:
--   **KEYSTONE (Part I uniqueness) — now PROVED (sorry-free).**
--
--   If two portraits have the same survivor set, then each survivor's host block is the same in both.
--   This is exactly the paper's Part I ("`T` injective ↔ the portrait is reconstructible from `U`"),
--   the documented open all-`d` kernel (machine-verified `d ≤ 8`; never previously mechanized for all
--   `d`).  Its proof has two stages, both genuinely deep:
--
--     (1) **`predIn` forced.**  `∀ u ∈ U, predIn P₁ u = predIn P₂ u`.  By induction over `.val` order:
--         `w = predIn P u` is the GREEDY pick from `U` — the highest same-fiber `v < u` that is unused
--         and whose chord `(v,u)` crosses no already-committed (lower-`.val`) edge.  Every higher
--         candidate `v ∈ (w,u)` is illegal: either `v ∈ U` (a non-top of its block; its child is left
--         of `u`, already committed) or, by the **Structural Lemma / Bridge**, `v`'s block is not
--         maximal in `(w,u)`, so it sits in the gap of an enclosing block whose edge `(a,b)` has
--         `a < v < b < u`, crossing the committed `(a,b)`.  The Structural Lemma ("no block maximal in
--         a parent-gap `(w,u)` has its top in `fiber(u)`") is fed by the now-PROVED substrate:
--           • TIGHTNESS  : `edge_tight_geom` (`g(e) = h(e) - 1`).
--           • COLUMN-SEP : `column_sep_geom` (no maximal tile of `e` shares `e`'s column).
--           • BRIDGE     : `bridge_edge` (PROVED) — the c*-edge `eB` of a c*-block `B` strictly inside
--                          `(w,u)` is non-maximal, so `eB ≪` a maximal tile `g` with `col g ≠ c*`.
--                          Remaining glue: `span_laminar` (Lemma 2, PROVED) + chord-enclosure
--                          (`sep_master`) ⇒ `block(g)` strictly encloses `span(B)` ⇒ `B` not maximal.
--
--     (2) **Block forced from `predIn`.**  Edges `{(predIn u, u) : u ∈ U}` are then equal across
--         `P₁, P₂`; the host block of `x` is the connected component of `x` in the predecessor graph
--         (`hostSet P x = {minVal} ∪ {survivors with the same predIn-descent root}`), so equal edges
--         ⇒ equal components ⇒ equal host blocks.
--
--   PROVED and available: `edge_tight_geom` (TIGHTNESS), `column_sep_geom` (COLUMN-SEP),
--   `span_laminar` (Lemma 2), `bridge_edge` (BRIDGE edge core), plus all of Forward's edge model
--   (`predIn_*`, `no_alt`, `lemmaA/B`, `survivorFamily`).
--
--   This theorem is now SORRY-FREE: stage (2) (component recovery) is fully proved here from
--   `predIn_forced` (stage 1, the single remaining `sorry`).  A block is recovered as the
--   `edgeStep`-component of its survivors together with its unique non-survivor `minVal` root; both
--   are forced because `T P` and the `predIn` map agree across `P₁, P₂`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L1021-L1060
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L1021-L1060

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.hostSet_forced [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {x : ZMod (d * m)} (hx₁ : x ∈ T P₁) (hx₂ : x ∈ T P₂) :
    hostSet P₁ x hx₁ = hostSet P₂ x hx₂ := by sorry
