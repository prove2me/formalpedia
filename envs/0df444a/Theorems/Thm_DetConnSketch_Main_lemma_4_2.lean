-- Prove2me | Theorems.Thm_DetConnSketch_Main_lemma_4_2
-- name    : DetConnSketch.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:02.988296+00:00
-- url     : https://prove2.me/theorems/33ab4cfd-5eeb-4e5d-8e12-2d33fdb0f1e6
-- title:
--   Lemma 4.2 — a one-sided linear sketch of $\tilde O(n\sqrt k)$ bits: equal sketches force each cut empty on one side to be empty or of size $>k$ on the other
-- statement:
--   There is a universal constant $C > 0$ such that for every $n$ and every real $0 \le k \le n^2$ there are an integer matrix $X \in \mathbb Z^{n\times D}$ with entries of absolute value at most $C(n+2)^C$, a finite field $\mathbb F_q$ with $q \le C(n+2)^C$ and a matrix $P \in \mathbb F_q^{n\times d}$, with $D + d \le C(\sqrt k+1)\log^C(n+2)$, such that the linear sketch $S(G) = (A_G X,\ A_G P)$ ($A_G$ the adjacency matrix) has the following property. For all graphs $G, H$ on $n$ vertices with $S(G) = S(H)$ and every cut $S \subseteq V$:
--   $$\text{1. } \delta_{G - G\cap H}(S) = 0 \Rightarrow \delta_{H - H\cap G}(S) = 0 \text{ or } \delta_{H - H\cap G}(S) > k;$$
--   $$\text{2. } \delta_{H - H\cap G}(S) = 0 \Rightarrow \delta_{G - G\cap H}(S) = 0 \text{ or } \delta_{G - G\cap H}(S) > k.$$
--   The sketch has $n(D+d)$ entries of $O(\log n)$ bits each, that is $\tilde O(n\sqrt k)$ bits.
--
--   Theorem 4.1 applies it with $k = 8\sqrt{n|E(F)|}$ at every level of the recursion.
--
--   Differences from the source:
--   - reading: a (linear) sketch S_one-sided which requires space Õ(n√k) → the pair (adjMat ℤ G · X, adjMat F G · P) with |X_ij| ≤ C (n+2)^C, |F| ≤ C (n+2)^C and D + d ≤ C (√k + 1)(log (n+2))^C, one universal C > 0; reason: the pair is linear in A_G and its n(D+d) entries take O(log(n+2)) bits each; for k ≥ 1 the dimension bound is Õ(√k). For 0 ≤ k < 1 replace both matrices by zero-column matrices: integer cut sizes are zero or > k, as the proof states. Thus the complete Õ(n√k) claim, including k = 0, follows
--   - encoding: G − G ∩ H, H − H ∩ G → G \ H and H \ G (SimpleGraph sdiff); reason: same graphs
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); reason: Lean indexing; same objects
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 20 (PDF 24), Lemma 4.2; p. 23 (PDF 27), proof

import Mathlib
import Definitions.Def_DetConnSketch_Main_CutSize
import Definitions.Def_DetConnSketch_Main_SketchMatrices

namespace DetConnSketch.Main

/-- Lemma 4.2 (linear sketch of `Õ(n√k)` bits, one universal constant `C`): for every `n` and
real `0 ≤ k ≤ n²` there are an integer matrix `X ∈ ℤ^{n×D}` with entries bounded by
`C (n+2)^C`, a finite field `F` with `|F| ≤ C (n+2)^C` and `P ∈ F^{n×d}`, with
`D + d ≤ C (√k + 1)(log (n+2))^C`, such that for all graphs `G, H` on `Fin n` with
`A_G X = A_H X` and `A_G P = A_H P`, every cut `S` satisfies:
(1) `δ_{G−G∩H}(S) = 0 → δ_{H−H∩G}(S) = 0 ∨ δ_{H−H∩G}(S) > k`;
(2) `δ_{H−H∩G}(S) = 0 → δ_{G−G∩H}(S) = 0 ∨ δ_{G−G∩H}(S) > k`. -/
theorem lemma_4_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (k : ℝ), 0 ≤ k → k ≤ (n : ℝ) ^ 2 →
      ∃ (D : ℕ) (X : Matrix (Fin n) (Fin D) ℤ) (F : Type) (_ : Field F) (_ : Fintype F)
        (d : ℕ) (P : Matrix (Fin n) (Fin d) F),
        (∀ i j, (|X i j| : ℝ) ≤ C * ((n : ℝ) + 2) ^ C) ∧
        (Fintype.card F : ℝ) ≤ C * ((n : ℝ) + 2) ^ C ∧
        ((D + d : ℕ) : ℝ) ≤ C * (Real.sqrt k + 1) * Real.log ((n : ℝ) + 2) ^ C ∧
        ∀ G H : SimpleGraph (Fin n),
          adjMat ℤ G * X = adjMat ℤ H * X → adjMat F G * P = adjMat F H * P →
          ∀ S : Finset (Fin n),
            (cutSize (G \ H) S = 0 →
              cutSize (H \ G) S = 0 ∨ k < (cutSize (H \ G) S : ℝ)) ∧
            (cutSize (H \ G) S = 0 →
              cutSize (G \ H) S = 0 ∨ k < (cutSize (G \ H) S : ℝ)) := by sorry

end DetConnSketch.Main
