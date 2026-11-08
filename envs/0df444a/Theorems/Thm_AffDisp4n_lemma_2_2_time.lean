-- Prove2me | Theorems.Thm_AffDisp4n_lemma_2_2_time
-- name    : AffDisp4n.lemma_2_2_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:20.796195+00:00
-- url     : https://prove2.me/theorems/0cba4a90-4ef5-4a9b-8834-5aee4d494d77
-- title:
--   Lemma 2.2, polynomial-time clause — a machine writes the point, the basis and the bit (existence clause: lemma_2_2)
-- statement:
--   There is one polynomial-time machine that takes a set $P$ of pairs of the parameters $u \in \mathbb F_2^m$ and an output form (i) or (ii) of Lemma 2.2, given by its affine functions, and writes a point $u_0$, linearly independent vectors $B$ and a bit $b$ with the following property. If $P$ consists of disjoint pairs and $a = m - |P| > d$, then
--   $$
--   u_0 + \operatorname{span} B \subseteq Z(P), \qquad |B| \ge a - 1 \;(\ge d),
--   $$
--   and the output equals $b$ on all of $u_0 + \operatorname{span} B$.
--
--   This is the polynomial-time clause of Lemma 2.2. The companion item `AffDisp4n.lemma_2_2` is the existence clause, the part the lower bound uses.
--
--   **Formalization Note** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime`, as in the published `PvsNP.P`.
--
--   Differences from the source:
--   - generalization: the output of C is (i) an affine function of the parameters or (ii) a literal of an AND-type gate whose two parents are affine functions of the parameters → any SimpleOutput m, an affine function or (ℓ₁ + α)(ℓ₂ + β) + γ, given by coefficients; reason: an output of either form computes such a function, and "given these affine functions" is the input
--   - generalization: a construction under the hypothesis a > d → one machine, chosen before d, that does not receive d; reason: the construction on p.17 never reads d; for a given d it is the printed statement
--   - encoding: we can construct in polynomial time → Nonempty (Turing.TM2ComputableInPolyTime encSimpleInput (fun l => l) F); reason: the paper fixes no machine or encoding; this is the machine of the published PvsNP.P, and the input length is polynomial in m and at least m
--   - encoding: an affine subspace U represented by a point and a basis, of dimension at least a − 1 ≥ d → a point u₀ and a linearly independent list B written in the output, with U = u₀ + span B and m − |P| − 1 ≤ |B|; reason: the dimension of u₀ + span B is |B|; a − 1 ≥ d follows from the hypothesis
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.5, p.17, Lemma 2.2

import Mathlib
import Definitions.Def_AffDisp4n_PairsDisjoint
import Definitions.Def_AffDisp4n_Z
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_AffDisp4n_vecWord
import Definitions.Def_AffDisp4n_pointBasisSubspace
import Definitions.Def_AffDisp4n_SimpleOutput
import Definitions.Def_AffDisp4n_encSimpleInput

namespace AffDisp4n

/-- **Lemma 2.2, polynomial-time clause** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), p.17): "Given these affine functions, we can construct in polynomial time an affine subspace U ⊆ Z(P) of dimension at least
a − 1 ≥ d which is represented by a point and a basis, and a constant b ∈ 𝔽₂ such that C(u⃗) = b for every
u⃗ ∈ U." One polynomial-time machine takes the set `P` and the affine functions of the output, and writes a
point `u₀`, a basis `B` and a bit `b`, such that for every set `P` of disjoint pairs with `a = m − |P| > d`,
the subspace `u₀ + span B` lies in `Z(P)`, has dimension at least `a − 1`, and the output is `b` on it. The
existence clause alone is the companion item `lemma_2_2`.

**Formalization Note** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime`, as in the published
`PvsNP.P`. The machine does not receive `d`. The encodings are `encSimpleInput` and `LowErrExt.encWords`. -/
theorem lemma_2_2_time :
    ∃ F : (Σ m, Finset (Sym2 (Fin m)) × SimpleOutput m) → List (Fin 3),
      Nonempty (Turing.TM2ComputableInPolyTime encSimpleInput (fun l : List (Fin 3) => l) F) ∧
      ∀ (m : ℕ) (P : Finset (Sym2 (Fin m))) (g : SimpleOutput m), PairsDisjoint P →
        ∀ d : ℕ, (d : ℤ) < (m : ℤ) - P.card →
        ∃ (u₀ : Fin m → ZMod 2) (B : List (Fin m → ZMod 2)) (b : ZMod 2),
          F ⟨m, (P, g)⟩ = LowErrExt.encWords (subspaceTokens u₀ B b) ∧
          LinearIndependent (ZMod 2) (fun i : Fin B.length => B.get i) ∧
          ((pointBasisSubspace u₀ B : AffineSubspace (ZMod 2) (Fin m → ZMod 2)) :
            Set (Fin m → ZMod 2)) ⊆ Z P ∧
          (m : ℤ) - P.card - 1 ≤ (B.length : ℤ) ∧
          ∀ u ∈ pointBasisSubspace u₀ B, g.eval u = b := by sorry

end AffDisp4n
