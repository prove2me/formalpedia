-- Prove2me | Theorems.Thm_AbelianCayleyHDX_lemma_3_2
-- name    : AbelianCayleyHDX.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:36:11.860213+00:00
-- url     : https://prove2.me/theorems/34ed2a2e-0d01-46fc-a4fa-97bc92aedf99
-- title:
--   Lemma 3.2 — explicit spanning direction sets with $\nu = O_q(t)$, $\Delta/\nu \ge (q-5)/(q-2)$, $\dim_F A(D) \ge 2^{t/3}$
-- statement:
--   Let $q = 2^h \ge 8$ be fixed and $F = \mathbb F_{q^2}$. For arbitrarily large integers $t$ one can explicitly construct a spanning set $D \subseteq \mathrm{PG}(t-1, F)$ such that, writing $\nu = |D|$ and $\Delta = \Delta(D)$,
--   $$\nu = O_q(t), \qquad \frac{\Delta}{\nu} \ge \frac{q-5}{q-2}, \qquad \dim_F A(D) \ge 2^{t/3}. \qquad (3.1)$$
--
--   Precisely: there are a constant $C > 0$ depending on $q$, a sequence $t_j \to \infty$ with $t_j \ge 1$, and spanning sets $D_j \subseteq \mathrm{PG}(t_j - 1, F)$ with $\nu_j \le C t_j$, $(q-5)\nu_j \le (q-2)\Delta(D_j)$ and $\dim_F A(D_j) \ge 2^{t_j/3}$; and for every binary encoding of the elements of $F$ there are one Turing machine and one polynomial $p$ such that the machine, given $j$ in binary, outputs $t_j$ and one nonzero representative of each direction of $D_j$ (each direction once) within $p(t_j)$ steps.
--
--   The proof (Section 4) uses a Garcia–Stichtenoth tower over $\mathbb F_{q^2}$.
--
--   Differences from the source:
--   - encoding: $F = \mathbb F_{q^2}$ → any finite field with $q^2$ elements; reason: all such fields are isomorphic to $\mathbb F_{q^2}$
--   - reading: for arbitrarily large integers $t$ one can explicitly construct $D$ → a sequence $t_j \to \infty$ and one machine producing $D_j$ from $j$ within time polynomial in $t_j$; reason: a construction for arbitrarily large $t$ is an infinite family; the output has $O(t^2)$ field elements, and the tower bases are computed in polynomial time [GX22] (p.15)
--   - reading: $\nu = O_q(t)$ → $\nu_j \le C t_j$ with $C$ depending on $q$ (quantified after $h$); reason: the $O_q$ constant may depend on $q$
--   - encoding: $\Delta/\nu \ge (q-5)/(q-2)$ → $(q-5)\nu \le (q-2)\Delta$; reason: multiplied out; $\nu \ge 1$ since $D$ spans $F^t$ with $t \ge 1$
--   - generalization: field elements encoded in binary (one fixed encoding) → the same family $D_j$ is explicit under every bijection $F \to \{0,\dots,q^2-1\}$; reason: specializes to any fixed encoding; the family is chosen before the encoding
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.2, p.12, Eq. (3.1)

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsSpanning
import Definitions.Def_AbelianCayleyHDX_Delta
import Definitions.Def_AbelianCayleyHDX_affineSpace
import Definitions.Def_AbelianCayleyHDX_encFVec
import Definitions.Def_HMBinPacking_OutputsWithin
open Filter RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX

/-- **Lemma 3.2** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.2, p.12, Eq. (3.1)). Let `q = 2^h ≥ 8` be fixed and
`F = 𝔽_{q²}`. For arbitrarily large integers `t` one can explicitly construct a spanning set
`D ⊆ PG(t − 1, F)` such that, with `ν = |D|` and `Δ = Δ(D)`,
$$\nu = O_q(t), \qquad \frac{\Delta}{\nu} \ge \frac{q-5}{q-2}, \qquad \dim_F A(D) \ge 2^{t/3}.$$

Stated as: there are a constant `C` (depending on `q`) and a sequence `t_j → ∞`, `t_j ≥ 1`, with
spanning sets `D_j` satisfying `ν ≤ C t_j`, `(q − 5) ν ≤ (q − 2) Δ` and `dim_F A(D_j) ≥ 2^{t_j/3}`,
and for every binary encoding of the field elements one Turing machine and one polynomial `p` such
that the machine, given `j` in binary, outputs `t_j` and one nonzero representative of each
direction of `D_j` (no direction twice) within `p(t_j)` steps.

**Formalization Note** `F` is any finite field with `q²` elements, its elements written in binary
through any bijection `enc : F ≃ {0, …, q² − 1}`. "Explicitly construct" is read as time
polynomial in `t` (the output has `O(t²)` field elements). The ratio bound is multiplied out
(`ν ≥ 1` since `D` spans `F^t`, `t ≥ 1`). -/
theorem lemma_3_2 (h : ℕ) (hq : 8 ≤ 2 ^ h) (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = (2 ^ h) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ t : ℕ → ℕ, Tendsto t atTop atTop ∧ (∀ j, 1 ≤ t j) ∧
      ∃ D : ∀ j, Finset (PG (t j) F),
        (∀ j, IsSpanning (D j) ∧ ((D j).card : ℝ) ≤ C * (t j : ℝ) ∧
          ((2 : ℝ) ^ h - 5) * ((D j).card : ℝ) ≤ ((2 : ℝ) ^ h - 2) * (Delta (D j) : ℝ) ∧
          (2 : ℝ) ^ ((t j : ℝ) / 3) ≤ (Module.finrank F (affineSpace (D j)) : ℝ)) ∧
        ∀ enc : F ≃ Fin (Fintype.card F), ∃ M : Turing.TM2ComputableAux Bool Bool,
          ∃ p : Polynomial ℕ, ∀ j, ∃ reps : List (Fin (t j) → F),
            reps.length = (D j).card ∧
            (∀ a ∈ reps, ∃ ha : a ≠ 0, Projectivization.mk F a ha ∈ D j) ∧
            (∀ d ∈ D j, ∃ a ∈ reps, ∃ ha : a ≠ 0, Projectivization.mk F a ha = d) ∧
            HMBinPacking.OutputsWithin M (encNat j) (encNat (t j) ++ encList (encFVec enc) reps)
              (p.eval (t j)) := by sorry

end AbelianCayleyHDX
