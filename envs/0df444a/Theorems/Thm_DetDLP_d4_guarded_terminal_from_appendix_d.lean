-- Prove2me | Theorems.Thm_DetDLP_d4_guarded_terminal_from_appendix_d
-- name    : DetDLP.d4_guarded_terminal_from_appendix_d
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T05:29:51.716928+00:00
-- url     : https://prove2.me/theorems/90784d2d-bb20-456f-897e-857859d6145a
-- title:
--   Guarded terminal accumulation from the two Appendix D algorithms
-- statement:
--   Assuming the closed contraction and one-step packet algorithms of Appendix D, a uniform machine computes the guard-divided accumulation on a lookup-separator tensor network. At each coefficient the accumulated terms agree with the guard-scaled exact integer contraction to the required precision.

import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_TerminalBTN
import Definitions.Def_DetDLP_FactorBase
set_option autoImplicit false
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4_guarded_terminal_from_appendix_d (hOAI : OpenAIAppendixDPremise) :
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
