-- Prove2me | Theorems.Thm_ClonableQMASep_Main_lemma_3
-- name    : ClonableQMASep.Main.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:07.439227+00:00
-- url     : https://prove2.me/theorems/3d30c867-ff77-41c9-b83c-92f24a96094c
-- title:
--   Lemma 3 — no-query guessing with classical side information
-- statement:
--   Let $C\subseteq\Sigma^n$ be a code satisfying the coordinate-symbol diversity bound (1) at an integer $L\ge1$ (every $L$ distinct codewords touch at least $nL/2$ coordinate-symbol pairs), let $t\ge0$ and $0<p\le1/2$. Let $\mathsf{Guesser}$ be any randomized or quantum procedure, fixed independently of $H$, that makes no queries and whose only $H$-dependent input is $w\in\{0,1\}^t$. Then
--   $$\mathbb E_{H\leftarrow\mathrm{Bias}_{n,p,\Sigma}}\Big[\max_{w\in\{0,1\}^t}\Pr_{T\leftarrow\mathsf{Guesser}(1^L,w)}[\mathsf{Valid}_H(T)]\Big]\le\min\{1,2^t(1-p)^{nL/2}\}.$$
--   In particular the same bound holds for any choice $w=w(H)$, and if $p=\lambda^{-4}$ and $n\ge\lambda^5$ the bound is at most
--   $$\min\{1,2^t(1-\lambda^{-4})^{\lambda^5L/2}\}.$$
--   No running-time bound on the guesser is required.
--
--   Lemma 3 is the information-theoretic core of the QCMA lower bound: a short classical witness cannot help produce many solutions to code intersection without queries.
--
--   Differences from the source:
--
--   - generalization: C = C_λ from an (r, L_max)-good family, sufficiently large λ, 1 ≤ L ≤ L_max → any code C ⊆ Σ^n over a finite alphabet satisfying diversity (1) at L ≥ 1, every λ; reason: the proof uses only (1) at this L; a good family satisfies (1) for 1 ≤ L ≤ L_max at large λ
--   - encoding: a randomized or quantum algorithm with no running-time bound, fixed independently of H → a kernel w ↦ sub-probability distribution on output tuples, chosen before H; reason: every finite output distribution is realized by some query-free procedure; missing mass is a failure output
--   - generalization: for the parameters of Theorem 4, p = λ^{−4} and L ≤ 2^λ → p = λ^{−4} and n ≥ λ^5 (no bound on L beyond diversity); reason: the specialization uses only n ≥ λ^5 (p. 17); Theorem 4's n = q ≥ λ^5
-- source:
--   Alper Cakan, Kai-Min Chung, Wei-Hsiang Hung, Tzu-Yi Yang, Separating ClonableQMA and QCMA Relative to a Classical Oracle, STOC 2027 submission #844 (October 2026), Lemma 3, p. 16

import Definitions.Def_ClonableQMASep_Main_Hash

set_option autoImplicit false

namespace ClonableQMASep.Main

/-- Lemma 3 (No-query guessing with classical side information, p. 16). Let `C ⊆ A^n` satisfy the
diversity bound (1) at `L ≥ 1`, let `t ≥ 0`, `0 < p ≤ 1/2`, and let `G` be a query-free guesser,
fixed independently of `H`, with a `t`-bit classical input. Then
`E_{H ← Bias_{n,p,A}}[max_w Pr_{T ← G(w)}[Valid_H(T)]] ≤ min{1, 2^t (1−p)^{nL/2}}`; the same bound
holds for any choice `w = w(H)`; and if `p = λ^{−4}` and `n ≥ λ^5`, the bound is at most
`min{1, 2^t (1 − λ^{−4})^{λ^5 L/2}}`. -/
theorem lemma_3 {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] (C : Set (Fin n → A))
    (L t : ℕ) (hL : 1 ≤ L) (hdiv : Diverse C L) (p : ℝ) (hp0 : 0 < p) (hp : p ≤ 1 / 2)
    (G : (Fin t → Bool) → (Fin L → (Fin n → Bool) × (Fin n → A)) → ℝ) (hG : IsGuesser G) :
    biasExp p (fun H => Finset.univ.sup' Finset.univ_nonempty
        (fun w => guessProb G w (Valid C H))) ≤
      min 1 ((2 : ℝ) ^ t * (1 - p) ^ ((n : ℝ) * L / 2)) ∧
    (∀ wH : HashFam n A → (Fin t → Bool),
      biasExp p (fun H => guessProb G (wH H) (Valid C H)) ≤
        min 1 ((2 : ℝ) ^ t * (1 - p) ^ ((n : ℝ) * L / 2))) ∧
    (∀ lam : ℕ, lam ^ 5 ≤ n → p = ((lam : ℝ) ^ 4)⁻¹ →
      biasExp p (fun H => Finset.univ.sup' Finset.univ_nonempty
          (fun w => guessProb G w (Valid C H))) ≤
        min 1 ((2 : ℝ) ^ t * (1 - ((lam : ℝ) ^ 4)⁻¹) ^ ((lam : ℝ) ^ 5 * L / 2))) := by sorry

end ClonableQMASep.Main
