-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_8
-- name    : DetSpectralSparsify.Dense.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:23.978864+00:00
-- url     : https://prove2.me/theorems/cb5fe469-e660-4618-b38a-db27df5d5f8d
-- title:
--   Lemma 8 (Inverse-square-root approximation) — degree O(a^{−1/2} log(2/(τ√a))), coefficient accuracy and DCT cost
-- statement:
--   There are an absolute constant $C>0$ and two fixed deterministic programs with the following property. Given $0<a\le1$ and $0<\tau<1/2$, the first program constructs $d+1$ distinct nodes $x_0,\ldots,x_d\in[a,2]$, where
--   $$d\le C a^{-1/2}\log\frac{2}{\tau\sqrt a}.$$
--   Whenever supplied values $y_k$ satisfy $|y_k-x_k^{-1/2}|\le\tau/(4(d+1))$, their interpolant $p$ has degree at most $d$ and
--   $$\sup_{t\in[a,2]}|p(t)-t^{-1/2}|\le\tau.$$
--   The second program computes the Chebyshev coefficients of that interpolant from $(d,a,y_0,\ldots,y_d)$, exactly for every vector $y$. Each program takes at most $C(d+1)\log(d+2)$ steps. Thus $d+1$ scalar inverse-square-root evaluations at the prescribed accuracy, together with the stated arithmetic work, construct the approximating polynomial.
--
--   This polynomial is used to approximate the inverse square root of the normalized Laplacian on its nonzero spectral subspace.
--
--   **Formalization Note** Both programs use the closed real RAM of `Machine`, so no arbitrary real constants or oracle operations are available. Interpolation is `Lagrange.interpolate`; `chebOnInterval` reads Chebyshev coefficients on $[a,2]$. The word-size exponent and programs are fixed before $(a,\tau)$.
--
--   Differences from the source:
--   - encoding: deg p ≤ d = O(a^{−1/2} log(2/(τ√a))) → an absolute C > 0, chosen before a and τ, bounds d and both computation costs; reason: the O-constants are uniform over all admissible a and τ; finitely many constants can be replaced by their maximum
--   - reading: one can deterministically construct p; d+1 scalar inverse-square-root evaluations with error τ/(4(d+1)) suffice → two fixed closed real-RAM programs generate d+1 nodes from (a,τ) and compute the Chebyshev coefficients of the interpolant from (d,a) and the supplied scalar values; the approximation bound holds for every admissible vector of values; reason: makes the computational clause uniform, rather than choosing nodes and advice separately for each input; the interpolation and error tolerance are those of Appendix A
--   - reading: O((d+1) log(d+2)) arithmetic operations → each of node generation and coefficient transformation takes at most C(d+1)log(d+2) steps on the mission RAM, including indexing and control; reason: the declared computation model counts actual operations; choosing a power-of-two number of Chebyshev nodes changes only the unspecified constant and permits root construction with arithmetic and square roots, without real constants, logarithm or cosine instructions
--   - encoding: a polynomial represented by its Chebyshev coefficients → node output has d in nat[0] and nodes in real[0..d]; coefficient input is paramInput [d] (a :: List.ofFn y), and output has d in nat[0] and coefficients in real[0..d]; reason: fixed input and output layouts; chebOnInterval converts coefficients to the polynomial on [a,2]
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.15, Lemma 8; restated and proved in Appendix A, pp.32–33

import Definitions.Def_DetSpectralSparsify_Dense_Machine

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 8 (Inverse-square-root approximation), pp.15, 32–33. Two fixed real-RAM
programs construct interpolation nodes and transform the supplied scalar evaluations into
Chebyshev coefficients. Both take O((d+1) log(d+2)) steps. The approximation holds for every
set of scalar values within τ/(4(d+1)) of the inverse square roots at the nodes. -/
theorem lemma_8 :
    ∃ (C : ℝ) (Pnodes Pcoeff : Program) (K : ℕ), 0 < C ∧
    ∀ a τ : ℝ, 0 < a → a ≤ 1 → 0 < τ → τ < 1 / 2 →
      ∃ (d : ℕ) (x : Fin (d + 1) → ℝ),
        (d : ℝ) ≤ C * (Real.sqrt a)⁻¹ * Real.log (2 / (τ * Real.sqrt a)) ∧
        Function.Injective x ∧ (∀ k, a ≤ x k ∧ x k ≤ 2) ∧
        -- Uniform construction of the nodes from (a, τ), with no real advice.
        (∃ (T : ℕ) (s' : State),
          RunsWithin Pnodes K 2 (paramInput [] [a, τ]) T s' ∧
          s'.nat 0 = d ∧ (∀ k, s'.real k.val = x k) ∧
          (T : ℝ) ≤ C * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 2)) ∧
        -- The advertised tolerance applies to every possible set of scalar evaluations.
        (∀ y : Fin (d + 1) → ℝ,
          (∀ k, |y k - (Real.sqrt (x k))⁻¹| ≤ τ / (4 * ((d : ℝ) + 1))) →
          (Lagrange.interpolate Finset.univ x y).natDegree ≤ d ∧
          ∀ t : ℝ, a ≤ t → t ≤ 2 →
            |(Lagrange.interpolate Finset.univ x y).eval t - (Real.sqrt t)⁻¹| ≤ τ) ∧
        -- A second fixed program computes the coefficients for all input values.
        (∀ y : Fin (d + 1) → ℝ, ∃ (T : ℕ) (s' : State),
          RunsWithin Pcoeff K (2 + d)
            (paramInput [d] (a :: List.ofFn y)) T s' ∧
          s'.nat 0 = d ∧
          chebOnInterval a d s'.real = Lagrange.interpolate Finset.univ x y ∧
          (T : ℝ) ≤ C * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 2)) := by sorry

end DetSpectralSparsify.Dense
