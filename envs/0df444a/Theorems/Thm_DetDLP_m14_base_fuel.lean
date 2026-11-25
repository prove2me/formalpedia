-- Prove2me | Theorems.Thm_DetDLP_m14_base_fuel
-- name    : DetDLP.m14_base_fuel
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T06:54:28.959904+00:00
-- url     : https://prove2.me/theorems/739da5f9-1986-5d8b-8ab5-fbf2ad0702b7
-- title:
--   Irreducible 0/1 modulus polynomial, input-slice field decoding, and fuel sufficiency bounds
-- statement:
--   Establishes three foundational components for deterministic D4 rank enumeration:
--
--   1. For $1 \le \mathrm{level}(S)$, `soloPoly S` is monic of degree $4 \lceil \log_2 S \rceil$, satisfies `RingOK`, and has coefficients in $\{0, 1\}$.
--   2. The `D4Slice.field 0..8` projections of `D4Plan.input x` recover $x.\mathrm{desc}$, $x.G.\mathrm{encode}$, $b, m, k, S, p, l$, and the lookup-vertex mask, and `fBitsRaw A (D4Plan.input x) = polynomialBits (soloPoly x.S)` under adequate fuel.
--   3. Standard `Nat.clog` upper bounds and fuel lower bounds showing `(polyUnits (A_fuel C K_loc) w).length` dominates $4mk$, $4\,\mathrm{level}(S)$, `pow2Level4 x.S`, $64^{\mathrm{shift}(x.S, d)}$, `guard + x.p`, `budget x.S D (8 K_loc)`, $x.l \cdot 4\,\mathrm{level}(S)$, and all graph degrees whenever $|\mathrm{input}(x)| \le |w|$.
-- source:
--   Deterministic Discrete Logarithms paper, Section 5.3 (Milestone 14 modular decomposition)

import Definitions.Def_DetDLP_D4SoloPlanDefs
set_option autoImplicit false
open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m14_base_fuel :
    (∀ {S : ℕ}, 1 ≤ D3Stopped.level S →
      (soloPoly S).Monic ∧ (soloPoly S).natDegree = 4 * Nat.clog 2 S ∧ RingOK (soloPoly S)) ∧
    (∀ (S i : ℕ), (soloPoly S).coeff i = 0 ∨ (soloPoly S).coeff i = 1) ∧
    (∀ {C c : ℕ} (x : Input C c),
      D4Slice.field 0 (D4Plan.input x) = x.desc ∧
      D4Slice.field 1 (D4Plan.input x) = x.G.encode ∧
      D4Slice.field 2 (D4Plan.input x) = countWord x.b ∧
      D4Slice.field 3 (D4Plan.input x) = countWord x.m ∧
      D4Slice.field 4 (D4Plan.input x) = countWord x.k ∧
      D4Slice.field 5 (D4Plan.input x) = countWord x.S ∧
      D4Slice.field 6 (D4Plan.input x) = countWord x.p ∧
      D4Slice.field 7 (D4Plan.input x) = countWord x.l ∧
      D4Slice.field 8 (D4Plan.input x) = List.ofFn (fun v : Fin x.G.nV => decide (v ∈ x.spec.lookupVerts))) ∧
    (∀ {C c : ℕ} (x : Input C c), 1 ≤ D3Stopped.level x.S → ∀ (A : ℕ),
      4 * D3Stopped.level x.S ≤ (polyUnits A (D4Plan.input x)).length →
      pow2Level4 x.S ≤ (polyUnits A (D4Plan.input x)).length →
      fBitsRaw A (D4Plan.input x) = polynomialBits (soloPoly x.S)) ∧
    (∀ {w : List Bool} {xs : List (List Bool)}, w ∈ xs → w.length ≤ (Encoding.encodeList id xs).length) ∧
    (∀ n : ℕ, Nat.clog 2 n ≤ n) ∧
    (∀ {n : ℕ}, 1 ≤ n → 2 ^ Nat.clog 2 n ≤ 2 * n) ∧
    (∀ {n : ℕ}, 2 ≤ n → 64 ^ Nat.clog 32 n ≤ (32 * n) ^ 2) ∧
    (∀ {C c : ℕ} (x : Input C c) (K_loc : ℕ) (w : Wd),
      (D4Plan.input x).length ≤ w.length →
      let F := (polyUnits (A_fuel C K_loc) w).length
      let D := Nat.clog 32 (4 * x.m)
      let guard := totalGuard x.S D
      4 * x.m * x.k ≤ F ∧
      4 * D3Stopped.level x.S ≤ F ∧
      pow2Level4 x.S ≤ F ∧
      (∀ d, 64 ^ D3Stopped.shift x.S d ≤ F) ∧
      guard + x.p ≤ F ∧
      D4UnrollBudget.budget x.S D (8 * K_loc) ≤ F ∧
      x.l * (4 * D3Stopped.level x.S) ≤ F ∧
      (∀ v₀ : Fin x.G.nV, x.G.deg v₀ ≤ F)) := by sorry
