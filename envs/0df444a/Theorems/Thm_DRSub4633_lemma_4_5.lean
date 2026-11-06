-- Prove2me | Theorems.Thm_DRSub4633_lemma_4_5
-- name    : DRSub4633.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:08:53.644051+00:00
-- url     : https://prove2.me/theorems/3e820d84-a0a4-4a41-96f3-3a441ced2156
-- title:
--   Lemma 4.5 — ordered large-coordinate comparison
-- statement:
--   Let $f$ be nonnegative, continuously differentiable and DR-submodular on $Q$, fix $x\in Q$, and use the objects of Section 4.1 (residual $F$, path $a(t)$, field components $g^L(t)$, prefix paths $Y_i$, $E=Y_0$, $y=Y_m$, $S_0$). For every $o_L\in[0,1]^L$ and $t\in[0,1]$,
--   $$F(a(t),o_L)\le C(t)+\langle g^L(t),\,o_L-v\rangle,\tag{31}$$
--   where
--   $$C(t)=\Lambda(q_m)y(t)-bS_0(t)-\vartheta(q_1)E(t)-\sum_{i=1}^{m-1}[\vartheta(q_{i+1})-\vartheta(q_i)]Y_i(t).\tag{32}$$
--
--   Differences from the source:
--   - encoding: objective defined on Q only; R^n with coordinatewise order; C^1 with boundary derivatives the continuous extensions of interior ones → f a total function on EuclideanSpace ℝ (Fin n), hypotheses on the cube only, values off the cube never read; the order written coordinatewise; GeomDRSub.IsDRSubmodular (ContDiffOn ℝ 1 on the cube, fderivWithin the cube); reason: Lean convention; on the cube the within-cube derivative of a C^1 function is the continuous extension of the interior derivative, so the instances are the same
--   - encoding: L includes a dummy coordinate of state 1, label 1, weight q = 1, zero field component → only the original coordinates are represented; the dummy enters as label 1 with q_1 = 1 and its zero terms are dropped; reason: F does not depend on the dummy coordinate (p.10), so every dropped term is zero; same instances
--   - encoding: block vectors o_S, o_L, r, l indexed by S and L → functions on Fin n of which only the relevant block is read (mergePt); reason: Lean convention; same instances
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma 4.5, p.16

import Mathlib
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_DRSub4633_Cconst
import Definitions.Def_DRSub4633_gLarge

namespace DRSub4633

/-- **Lemma 4.5 (Ordered large-coordinate comparison).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma 4.5, p.16: "For every
`o_L ∈ [0, 1]^L` and `t ∈ [0, 1]`, `F(a(t), o_L) ≤ C(t) + ⟨g^L(t), o_L − v⟩`, (31) where `C(t)` is
(32)."

Standing hypotheses (Sections 3.1 and 4.1, pp.7–10): `f` nonnegative, `C¹` and DR-submodular on
`Q = [0, 1]^n`; `x ∈ Q` is the fixed state.

**Formalization Note.** `o_L` is a function on `Fin n`; only its large coordinates are read. The
dummy coordinate's term in `⟨g^L(t), o_L − v⟩` is zero (its component vanishes) and is dropped, as
is its value in `o_L` (`F` does not depend on it). -/
theorem lemma_4_5 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf0 : ∀ y ∈ GeomDRSub.cube n, 0 ≤ f y) (hf : GeomDRSub.IsDRSubmodular f)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ GeomDRSub.cube n)
    (oL : Fin n → ℝ) (hoL : ∀ j, sPar < x j → 0 ≤ oL j ∧ oL j ≤ 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    resid f x (mergePt x (aPath x t) oL) ≤
      Cconst f x t + ∑ j ∈ Finset.univ.filter (fun j : Fin n => sPar < x j),
        gLarge f x t j * (oL j - x j) := by sorry

end DRSub4633
