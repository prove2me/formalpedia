-- Prove2me | Theorems.Thm_DetANN_Thm11_outer_qry_spec
-- name    : DetANN.Thm11.outer_qry_spec
-- status  : Open
-- author  : @milia
-- created : 2026-11-23T21:58:21.845195+00:00
-- url     : https://prove2.me/theorems/625c1706-d156-44f9-9bd8-b21741ff517d
-- title:
--   Theorem 1.1, outer query: time and local answers from the stored state
-- statement:
--   Let $\mathrm{Pre}_3,\mathrm{Qry}_3$ be deterministic programs that satisfy $\mathrm{InnerSpec}(\mathrm{Pre}_3,\mathrm{Qry}_3,C,K,C_p)$ (definition `DetANN_Thm11_Stored`, the guarantees of Lemma 3.3) with $C>1$, and let $C_b\ge C$ be an integer. Let the inner program that this half of the outer structure runs ($\mathrm{Pre}_3$ for preprocessing, $\mathrm{Qry}_3$ for queries) use only registers below $n_3$ (`UsesBelow`) and have integer literals of absolute value at most $X_3\ge1$ (`LitBound`). Write $\mathrm{outerPre}$ and $\mathrm{outerQry}$ for the programs of definition `DetANN_Thm11_OuterProg` with these parameters and a literal $c_0$.
--
--   Then there is $c_0^{\min}$ such that for every $c_0\ge c_0^{\min}$ there are constants $C_q,K_q$ with the following property. Take an instance with $n\ge2$, $1\le d\le n$, injective $P:[n]\to\mathbb R^d$ and $\varepsilon\in(0,1)$, together with $k$, $C_0\ge c_0$ and a state $s$ satisfying $\mathrm{OuterStored}(\mathrm{Pre}_3,X_3,\mathrm{innerQT},P,\varepsilon,C_0,k,s)$. Then for every query $q\in\mathbb R^d$, $\mathrm{outerQry}$ started on the query layout of $q$ over $s$ halts after some $t'$ steps with work at most
--   $$C_q\big(d^2+d\,\varepsilon^{-K_q}(1+\log n)^{K_q}\big),$$
--   and its answer pointer $0$ holds an index $a$ with $\mathrm{LocalAnswer}(C_0,k,P,\varepsilon,q,a)$ (definition `DetANN_Thm11_Split`).
--
--   This is the query half of the machine part of Theorem 1.1 (theorem `outer_composition`).
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' for the machine part of DetANN.theorem_1_1 (Feng, Indyk, STOC 2027 submission, Theorem 1.1, p.2; the construction of §7.4, p.19). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily
import Definitions.Def_DetANN_Thm11_Split
import Definitions.Def_DetANN_Thm11_OuterProg
import Definitions.Def_DetANN_Thm11_Stored

namespace DetANN

namespace Thm11

open PNormReg PNormRegLib

/-- **The outer query (Q).** For an inner pair with the guarantees of Lemma 3.3 (register bound `n3`,
literal bound `X3`, constants `C ≤ Cb`, `K`, `Cp`) there is a threshold `c0min` such that for every
literal `c0 ≥ c0min` there are constants `Cq, Kq` with: for every instance with `n ≥ 2`, every
padding `k`, every `C₀ ≥ c0` and every state `s` that is `OuterStored`, every query `q` is
answered by the outer query program within `Cq·(d² + d ε^{−Kq}(1 + log n)^{Kq})` steps, with a local
answer. -/
theorem outer_qry_spec :
    ∀ (Pre₃ Qry₃ : Program), DetProgram Pre₃ → DetProgram Qry₃ →
      ∀ (n3 X3 : ℕ), UsesBelow Qry₃ n3 n3 → LitBound Qry₃ X3 → 1 ≤ X3 →
        ∀ (C : ℝ) (K Cp Cb : ℕ), 1 < C → C ≤ Cb → InnerSpec Pre₃ Qry₃ C K Cp →
          ∃ c0min : ℕ, ∀ c0 : ℕ, c0min ≤ c0 → ∃ Cq Kq : ℕ, ∀ d n : ℕ, 1 ≤ d → d ≤ n → 2 ≤ n →
            ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
              ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (k : ℕ) (C₀ : ℝ) (s : State), (c0 : ℝ) ≤ C₀ →
                OuterStored Pre₃ X3 (innerQT Cp C₀ k P ε) P ε C₀ k s →
                ∀ q : EuclideanSpace ℝ (Fin d), ∃ t' : ℕ,
                  (run (outerQry Qry₃ n3 c0 Cb K Cp X3) (queryState d s q) detTape t').halted = true ∧
                  ((run (outerQry Qry₃ n3 c0 Cb K Cp X3) (queryState d s q) detTape t').work : ℝ) ≤
                    (Cq : ℝ) * ((d : ℝ) ^ 2 + d * ε⁻¹ ^ Kq * (1 + Real.log n) ^ Kq) ∧
                  ∃ a : Fin n,
                    (run (outerQry Qry₃ n3 c0 Cb K Cp X3) (queryState d s q) detTape t').core.ptrs 0 =
                      (a : ℤ) ∧ LocalAnswer C₀ k P ε q a := by
  sorry

end Thm11

end DetANN
