-- Prove2me | Theorems.Thm_BollobasChromatic_Main_lemma_1
-- name    : BollobasChromatic.Main.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:53:47.248986+00:00
-- url     : https://prove2.me/theorems/5fa5f823-b54d-449d-9b25-aab7eb820df6
-- title:
--   Lemma 1, p. 50 — martingale with |X_{k+1} − X_k| ≤ c: P(X_m ≤ E(X_m) − a) ≤ (b/(a+b))^{a+b} e^a ≤ exp{−a²/2(a+b)}
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\mathcal F_0\subset\mathcal F_1\subset\cdots$ an increasing sequence of sub-$\sigma$-fields of $\mathcal F$, and $X_0,X_1,\dots$ real random variables such that $X_k$ is $\mathcal F_k$-measurable and integrable and $\mathbb E(X_{k+1}\mid\mathcal F_k)=X_k$ (a martingale). Assume $X_0$ is almost surely constant. Suppose $|X_{k+1}-X_k|\le c$ almost surely for every $k$, for some $c>0$. Let $m\ge 0$, $b=mc^2$ and $a>0$. Then
--   $$
--   \mathbb P\bigl(X_m\le \mathbb E(X_m)-a\bigr)\;\le\;\Bigl(\frac{b}{a+b}\Bigr)^{a+b}e^{a}\;\le\;\exp\Bigl\{-\frac{a^2}{2(a+b)}\Bigr\}.
--   $$
--
--   This is the lower-tail martingale inequality the paper attributes to Freedman; the paper applies it to the edge-exposure martingale of the packing number $X$ to obtain (5).
--
--   **Formalization Note** The page allows an arbitrary $\mathcal F_0$; the hypothesis that $X_0$ is almost surely equal to its mean is added. Without it the statement is false: for $m=0$ we have $b=0$ and the bound is $0$, while $\mathbb P(X_0\le\mathbb E X_0-a)>0$ for a suitable non-constant $X_0$. In the paper's application $\mathcal F_0$ is trivial ($E_0=\emptyset$), so $X_0$ is constant there. The power $(\cdot)^{a+b}$ is the real power, with $0^{a}=0$ for $a>0$.
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), p. 50, Lemma 1, display (3)

import Mathlib

namespace BollobasChromatic.Main

open MeasureTheory

theorem lemma_1 {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (hX : Martingale X ℱ P)
    (hX0 : ∀ᵐ ω ∂P, X 0 ω = ∫ ω', X 0 ω' ∂P)
    (c : ℝ) (hc : 0 < c) (hbd : ∀ k, ∀ᵐ ω ∂P, |X (k + 1) ω - X k ω| ≤ c)
    (m : ℕ) (a : ℝ) (ha : 0 < a) :
    let b : ℝ := (m : ℝ) * c ^ 2
    P.real {ω | X m ω ≤ (∫ ω', X m ω' ∂P) - a} ≤ (b / (a + b)) ^ (a + b) * Real.exp a ∧
      (b / (a + b)) ^ (a + b) * Real.exp a ≤ Real.exp (-(a ^ 2 / (2 * (a + b)))) := by sorry

end BollobasChromatic.Main
