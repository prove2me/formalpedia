-- Prove2me | Theorems.Thm_DetDLP_guarded_terminal_digit_contraction
-- name    : DetDLP.guarded_terminal_digit_contraction
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T11:13:23.452268+00:00
-- url     : https://prove2.me/theorems/da14d803-d3b9-4f58-97eb-4caf60f814ae
-- title:
--   Guarded coefficient accumulation on lookup-separator networks
-- statement:
--   Assuming the scalar degree-sensitive contractor in Lemma 5.2, a uniform machine handles lookup-separator networks with integer coefficient-vector entries. For every retained coefficient, a finite sum of integer mode contributions is congruent to the contraction coefficient multiplied by a power of two at the correspondingly increased precision. The machine produces the quotients of the canonical accumulated residues by the guard power, in polynomial space and with exponent proportional to b/m plus b/sqrt(logSafe m). The outstanding construction is the terminal-preserving expansion, digit contraction and machine implementation.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Sections 5.3–5.4, proof of Theorem 4.3 (intermediate machine specification).

import Mathlib
import Definitions.Def_DetDLP_FactorBase
import Definitions.Def_DetDLP_TerminalBTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem guarded_terminal_digit_contraction
    (hscalar :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ'),
            2 ≤ β →
            1 ≤ Told →
            G.nE ≤ C * β →
            G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β →
            1 ≤ ℓ' → ℓ' ≤ C * β →
            BTNEntryEvaluable desc G P ℓ' T E outE (Told : ℝ) (((β + desc.length : ℕ) : ℝ) ^ c0) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            ∃ w : List Bool,
              EncodesTruncPoly P ℓ' w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
                (polyBound K (β + desc.length) * (Told : ℝ) *
                  (2 : ℝ) ^ ((K : ℝ) * (β : ℝ) / Real.sqrt (ρ : ℝ)))
                (polyBound K (β + desc.length))) :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (b m k S P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ → ℕ),
            2 ≤ b →
            1 ≤ m → 1 ≤ k →
            blockCount b ≤ C * m → m ≤ C * blockCount b →
            S ≤ C * m * b →
            4 * m * k ≤ C * b → b ≤ C * (4 * m * k) →
            1 ≤ P0 → P0 ≤ S →
            1 ≤ ℓ → ℓ ≤ C * m →
            G.nV ≤ (S + desc.length + 1) ^ c0 →
            ∀ (spec : LookupSeparatorSpec G m k S (C * Nat.ceil ((b : ℝ) ^ ((3 : ℝ) / 4)))),
            (∀ v t i, A v t i < 2^P0) →
            (∀ v t, RunsWithin E outE (encodePortQuery desc v.val (List.ofFn t))
              (encodeNatListBin (List.ofFn (A v t))) (polyBound c0 (S+desc.length))
              (polyBound c0 (S+desc.length))) →
            let Z := BTNContract G (fun v t => ∑ i : Fin ℓ,
              Polynomial.monomial i.val (A v t i : ℤ))
            ∃ (guard modes : ℕ) (terms : Fin modes → Fin ℓ → ℤ),
              (∀ i, (∑ ν, terms ν i) ≡ (2:ℤ)^guard * Z.coeff i.val
                [ZMOD (2:ℤ)^(guard+P0)]) ∧
              RunsWithin M outM (encodeTerminalBTNInstance desc G b m k S P0 ℓ spec.lookupVerts)
                (encodeNatListBin (List.ofFn fun i =>
                  ((∑ ν, terms ν i : ℤ) : ZMod (2^(guard+P0))).val / 2^guard))
                (polyBound K (S+desc.length) * (2:ℝ)^((K:ℝ)*
                  ((b:ℝ)/m+(b:ℝ)/Real.sqrt (logSafe m))))
                (polyBound K (S+desc.length)) := by sorry

end DetDLP
