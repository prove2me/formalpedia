-- Prove2me | Theorems.Thm_CopylessCRA_lemma_16
-- name    : CopylessCRA.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:51.021774+00:00
-- url     : https://prove2.me/theorems/b6515015-0965-479a-a476-f88966d8a942
-- title:
--   Display (4) and Lemma 16, p.11 — telescoping $M_w=\prod c(g_{i-1},a_i)\,M_{r_{g_n}}$ and $\prod c=\tau_i\exp(Z_i)$
-- statement:
--   1. (Display (4)) Let $M_a$ be invertible rational matrices, $\varphi:\Sigma^*\to F$ a monoid homomorphism into a group, and $r_g$ ($g\in F$) words with $r_1=\varepsilon$. Put $c(g,a)=M_{r_g}M_aM_{r_{g\varphi(a)}}^{-1}$. For $w=a_1\cdots a_n$, $g_0=1$ and $g_i=\varphi(a_1\cdots a_i)$,
--   $$M_w=c(g_0,a_1)c(g_1,a_2)\cdots c(g_{n-1},a_n)M_{r_{g_n}}.\tag{4}$$
--   2. (Lemma 16) Let $\mathfrak u$ be a $\mathbb Q$-space of pairwise commuting nilpotent $d\times d$ matrices, $t_1,t_2,\dots$ invertible with $t_i^{-1}\mathfrak ut_i\subseteq\mathfrak u$, and $X_1,X_2,\dots\in\mathfrak u$. With $\tau_0=I$, $Z_0=0$, $\tau_i=\tau_{i-1}t_i$ and $Z_i=t_i^{-1}Z_{i-1}t_i+X_i$,
--   $$t_1\exp(X_1)\cdots t_i\exp(X_i)=\tau_i\exp(Z_i)\qquad\text{for every } i .$$
--   In the paper $c(g_{i-1},a_i)=t_{g_{i-1},a_i}\exp(X_{g_{i-1},a_i})$ with $t\in T(\mathbb Q)$, $X\in\mathfrak u=\log U$.
--
--   Differences from the source:
--   - generalization: $\varphi$ the quotient map $\Sigma^*\to F=\Gamma/\Gamma^\circ$, $\varphi(r_g)=g$ → any monoid homomorphism into a group, any words $r_g$ with $r_1=\varepsilon$; reason: the telescoping uses only multiplicativity of $\varphi$ and $r_1=\varepsilon$
--   - generalization: $t_i=t_{g_{i-1},a_i}\in T(\mathbb Q)$, $X_i\in\mathfrak u=\log U$ from Lemma 5 under (C3) → any invertible $t_i$ and any $X_i$ in a $\mathbb Q$-space of commuting nilpotent matrices normalized by the $t_i$; reason: the proof uses only that $\mathfrak u$ is commutative and normalized by $T$; the paper's data satisfy this
--   - encoding: $\exp$ of a nilpotent matrix → the truncated series $\sum_{l<d}X^l/l!$; reason: exp of a nilpotent $d\times d$ matrix truncates after degree $d-1$ (p.12)
--   - generalization: words over a (finite) alphabet $\Sigma$ → words over any type $\alpha$ of letters (no finiteness assumed); reason: the telescoping and the induction are word by word and never use finiteness of the alphabet; a finite alphabet is a special case
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), display (4) and Lemma 16, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_CopylessCRA_IsRep
import Definitions.Def_CopylessCRA_IsSplitTorusQ

namespace CopylessCRA

/-- **Display (4) and Lemma 16.** With `c(g, a) = M_{r_g} M_a M_{r_{gφ(a)}}⁻¹`, for `w = a₁⋯aₙ`,
`g₀ = 1` and `g_i = φ(a₁⋯a_i)`, telescoping gives
`M_w = c(g₀, a₁) c(g₁, a₂) ⋯ c(g_{n−1}, aₙ) M_{r_{gₙ}}` (4).
Writing `c(g_{i−1}, a_i) = t_i exp(X_i)` and `τ₀ = I`, `Z₀ = 0`, `τ_i = τ_{i−1} t_i`,
`Z_i = t_i⁻¹ Z_{i−1} t_i + X_i`: `c(g₀, a₁) ⋯ c(g_{i−1}, a_i) = τ_i exp(Z_i)` for every `i`
(Lemma 16).

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), display (4) and Lemma 16, p.11 (PDF p.13).

**Formalization Note** In the paper `φ : Σ* → F = Γ/Γ°` is the quotient map, `r_g` are words with
`φ(r_g) = g` and `r_1 = ε`, `t_i ∈ T(ℚ)` and `X_i ∈ 𝔲 = log U`. The statement is made in the
generality its proof uses (a generalization): (4) for any monoid homomorphism `φ` from words to a
group and any words `r_g` with `r_1 = ε`; Lemma 16 for any invertible `t_i` and any `X_i` in a
`ℚ`-space `𝔲` of pairwise commuting nilpotent matrices normalized by every `t_i`. `exp` of a
nilpotent `d × d` matrix is the truncated series `nexp` (p.12). Products are left to right. -/
theorem lemma_16 {α : Type*} {d : ℕ} (M : α → Matrix (Fin d) (Fin d) ℚ) (hM : ∀ a, IsUnit (M a))
    {F : Type*} [Group F] (φ : FreeMonoid α →* F) (rw : F → List α) (hr1 : rw 1 = []) :
    (∀ w : List α, wordMat M w =
      (List.ofFn fun i : Fin w.length =>
        wordMat M (rw (φ (FreeMonoid.ofList (w.take i)))) * M (w.get i) *
          (wordMat M (rw (φ (FreeMonoid.ofList (w.take i)) * φ (FreeMonoid.of (w.get i)))))⁻¹).prod *
        wordMat M (rw (φ (FreeMonoid.ofList w)))) ∧
    ∀ (𝔲 : Submodule ℚ (Matrix (Fin d) (Fin d) ℚ)), (∀ Y ∈ 𝔲, IsNilpotent Y) →
      (∀ Y ∈ 𝔲, ∀ Y' ∈ 𝔲, Commute Y Y') →
      ∀ (tt : ℕ → (Matrix (Fin d) (Fin d) ℚ)ˣ) (X : ℕ → Matrix (Fin d) (Fin d) ℚ),
      (∀ i, X i ∈ 𝔲) →
      (∀ i, ∀ Y ∈ 𝔲, (((tt i)⁻¹ : (Matrix (Fin d) (Fin d) ℚ)ˣ) : Matrix (Fin d) (Fin d) ℚ) * Y *
        (tt i : Matrix (Fin d) (Fin d) ℚ) ∈ 𝔲) →
      ∀ (τ Z : ℕ → Matrix (Fin d) (Fin d) ℚ), τ 0 = 1 → Z 0 = 0 →
      (∀ i, τ (i + 1) = τ i * (tt (i + 1) : Matrix (Fin d) (Fin d) ℚ)) →
      (∀ i, Z (i + 1) = (((tt (i + 1))⁻¹ : (Matrix (Fin d) (Fin d) ℚ)ˣ) : Matrix (Fin d) (Fin d) ℚ) *
          Z i * (tt (i + 1) : Matrix (Fin d) (Fin d) ℚ) + X (i + 1)) →
      ∀ i, ((List.range i).map fun k =>
          (tt (k + 1) : Matrix (Fin d) (Fin d) ℚ) * nexp (X (k + 1))).prod = τ i * nexp (Z i) := by sorry

end CopylessCRA
