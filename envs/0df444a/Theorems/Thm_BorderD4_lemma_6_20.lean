-- Prove2me | Theorems.Thm_BorderD4_lemma_6_20
-- name    : BorderD4.lemma_6_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:50.872094+00:00
-- url     : https://prove2.me/theorems/0c8be5bf-4ba3-4442-8b9f-29c54f3ec67c
-- title:
--   Lemma 6.20: $P_{k+1,n}(b+(u,g))$ is nonzero with high-support monomials
-- statement:
--   Let $T\subseteq[N]$, $N=(k+1)n$, with $C:=N-|T|\le k$, let $u=x_T$, $b\in F^N$ and $g_a\in F[[u]]$ for $a\notin T$. If $n>C+|\mathrm{supp}(b)|$, then
--   $$f:=P_{k+1,n}(b+(u,g))\in F[[u]]$$
--   is nonzero, and every monomial occurring in $f$ involves at least $n-C-|\mathrm{supp}(b)|$ variables. These are the only two facts about $P_{k+1,n}$ that the lower bound uses.
--
--   Differences from the source:
--   - generalization: §6's standing field, algebraically closed of characteristic $0$ (p.49) → any field; reason: the proof uses only that block monomials have coefficient $1$; the source is an instance
--   - encoding: the variables $x_1,\dots,x_N$ → $\mathrm{Fin}(k+1)\times\mathrm{Fin}\,n$; reason: this is $P_{k+1,n}$ up to renaming
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.20, p.75

import Mathlib
import Definitions.Def_BorderD4_sumProduct
import Definitions.Def_BorderD4_evalAt
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- Lemma 6.20: let `T ⊆ [N]` with `C := N − |T| ≤ k`, `u := x_T`, `b ∈ F^N`, and `g_a ∈ F[[u]]` for `a ∉ T`. If
`n > C + |supp(b)|`, then `f := P_{k+1,n}(b + (u, g)) ∈ F[[u]]` is nonzero, and every monomial occurring in `f` involves
at least `n − C − |supp(b)|` variables.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.20, p.75. -/
theorem lemma_6_20 {F : Type*} [Field F] {k n : ℕ} (_hk : 1 ≤ k) (T : Finset (Fin (k + 1) × Fin n))
    (hT : Fintype.card (Fin (k + 1) × Fin n) - T.card ≤ k) (b : Fin (k + 1) × Fin n → F)
    (g : {a // a ∉ T} → MvPowerSeries T F)
    (hn : Fintype.card (Fin (k + 1) × Fin n) - T.card + (Function.support b).ncard < n) :
    aeval (uShift T b g) (sumProduct F k n) ≠ 0 ∧
    ∀ m : T →₀ ℕ, MvPowerSeries.coeff m (aeval (uShift T b g) (sumProduct F k n)) ≠ 0 →
      n - (Fintype.card (Fin (k + 1) × Fin n) - T.card) - (Function.support b).ncard ≤
        m.support.card := by sorry

end BorderD4
