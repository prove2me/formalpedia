-- Prove2me | Theorems.Thm_DeMorganApprox_Main_lemma_4_1
-- name    : DeMorganApprox.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:57.062168+00:00
-- url     : https://prove2.me/theorems/e1d8d91d-5ab7-4647-9759-9d6e1dd76e2b
-- title:
--   Lemma 4.1 — a span program with balanced bound S and ‖abs(V)‖ = O(1) gives degree O(S), ℓ1-norm 2^{O(S)}
-- statement:
--   Let a vector-form span program on the inputs $x_1,\dots,x_m$ compute a Boolean function $f$ and have balanced witness bound at most $S$, where $S\ge1$. Let $V$ be the matrix whose columns are all its listed vectors, and suppose $\|\operatorname{abs}(V)\|=O(1)$, i.e. $\|\operatorname{abs}(V)\|\le K$ for a fixed $K$. Then there is a real multilinear polynomial $P$ with
--   $$|P(x)-f(x)|\le\frac13\quad\text{for all }x\in\{0,1\}^m,$$
--   $$\deg P=O(S),\qquad\|P\|_1\le2^{O(S)},$$
--   where the constants in $O(\cdot)$ depend only on $K$.
--
--   This is the extraction step: Lemmas 5.7 and 5.9 supply its hypotheses with $S=O(\sqrt n)$, which yields the main theorem.
--
--   Differences from the source:
--   - reading: ‖abs(V)‖ = O(1), deg P = O(S), ‖P‖₁ ≤ 2^{O(S)} → for every K ≥ 0 there is C > 0, chosen before m, ι, J, the program, f and S, such that ‖abs(V)‖ ≤ K implies totalDegree P ≤ C·S and coeffL1 P ≤ 2^{C·S}; reason: the O(1) hypothesis is a fixed bound K, and the conclusion's constants may depend on that bound only
--   - reading: a real polynomial P with ‖P‖₁ taken after multilinearization on the Boolean cube (§3.1) → a multilinear P : MvPolynomial (Fin m) ℝ and coeffL1 P; reason: §3.1 defines ‖P‖₁ in the multilinear form, and the proof ends by multilinearizing, which preserves values on the cube and does not increase degree or norm
--   - encoding: inputs x ∈ {0,1}^m and values F(x) ∈ {0,1} → x : Fin m → Bool, the polynomial evaluated at the 0/1 real point boolPoint x, the value boolVal (F x) ∈ {0,1}; reason: the same Boolean cube and the same real values
--   - encoding: a real Euclidean space H with unit vectors and the entrywise absolute value abs(V) → the coordinate space ι → ℝ for a finite type ι with its standard basis; squared norms are sums of squares; reason: abs(V) is only defined relative to a fixed orthonormal basis, which the construction provides (leaf and helper coordinates); finitely many listed vectors span a finite-dimensional subspace
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Lemma 4.1, PDF p. 11 (printed p. 9), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; proof PDF pp. 12–16 (printed pp. 10–14)

import Mathlib
import Definitions.Def_DeMorganApprox_Main_SpanPrograms

namespace DeMorganApprox.Main

/-- Lemma 4.1, PDF p. 11 (printed p. 9); proof PDF pp. 12–16. `‖abs(V)‖ = O(1)` is a bound `K`
on the full matrix; the constant `C` depends only on `K`. -/
theorem lemma_4_1 (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) {ι J : Type} [Fintype ι] [Fintype J] (P : SpanProgram m ι J)
        (f : (Fin m → Bool) → Bool) (S : ℝ), 1 ≤ S →
        P.IsVectorForm → P.Computes f → P.HasBalancedBound S → AbsNormLE P.vec K →
        ∃ Q : MvPolynomial (Fin m) ℝ, IsMultilinear Q ∧
          (∀ x : Fin m → Bool, |MvPolynomial.eval (boolPoint x) Q - boolVal (f x)| ≤ 1 / 3) ∧
          (Q.totalDegree : ℝ) ≤ C * S ∧
          coeffL1 Q ≤ (2 : ℝ) ^ (C * S) := by sorry

end DeMorganApprox.Main
