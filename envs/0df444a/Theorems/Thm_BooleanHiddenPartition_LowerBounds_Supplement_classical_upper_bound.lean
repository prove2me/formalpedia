-- Prove2me | Theorems.Thm_BooleanHiddenPartition_LowerBounds_Supplement_classical_upper_bound
-- name    : BooleanHiddenPartition.LowerBounds.Supplement.classical_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:15:19.594001+00:00
-- url     : https://prove2.me/theorems/ba7fed6e-8e74-487c-90fe-cfd7d2cf8223
-- title:
--   Theorem 12 — Classical private-coin communication upper bound
-- statement:
--   There is one absolute constant $A>0$ with the following property. Fix $\alpha\in(0,1)$, positive integers $k,n,m$ with $km=\alpha n$, and $1\le d\le k$. Let $f:\{\pm1\}^k\to\{\pm1\}$ have sign degree exactly $d$. Let $p$ be any real polynomial of total degree $d$ that strictly sign-represents $f$ and satisfies $|p(z)|\le1$ on the whole sign cube. Write $\beta=\min_z|p(z)|>0$ and $\|\widehat p\|_1=\sum_{T\subseteq[k]}|\mathbb E_z[p(z)\chi_T(z)]|$, with uniform expectation. For every $0<\varepsilon<1/2$, there are a natural number $c$ and a private-coin one-way classical protocol solving the full ordered-block $f$-BHP promise problem with success at least $1-\varepsilon$ on every promised input, such that
--
--   $$c\le A\left[\left(\frac{k\|\widehat p\|_1^2}{\alpha\beta^2}\right)^{1/d}n^{1-1/d}\log(1/\varepsilon)+\log n\right].$$
--
--   The constant $A$ is independent of $\alpha,k,n,m,f,p,d,\varepsilon$, the input and the protocol. The spectral norm and margin are computed from the supplied polynomial, rather than free parameters. This companion theorem gives the classical upper bound alongside the published lower-bound goal; it is not used in the proof of that goal.
--
--   **Formalization Note** The bit budget is the integer $c$, so the message has at most $2^c$ possible values. The decoder may use independent private coins. The stated degree range includes $d=1$.
--
--   Differences from the source:
--   - encoding: sign-valued strings and ordered blocks with k dividing αn → the published Bool cube and Layout k n m α with km = αn; reason: true codes −1, coordinates are zero based, and all positive admissible layouts are preserved
--   - encoding: finite sign degree d → signDegree f = (d : WithTop ℕ); reason: the published least-degree definition represents the same finite degree
--   - encoding: O of the displayed communication expression with a fixed logarithm base → a positive existential multiplicative constant and natural logarithms; reason: changing a fixed logarithm base only rescales the permitted constant
--   - encoding: the exponent 1/d in Theorem 12 → 1 ≤ d explicitly; reason: the printed inverse-degree formula has defined domain d > 0, as in the brief; constant functions with degree zero are outside that formula
--   - encoding: a degree-d polynomial, its cube Fourier norm and its positive minimum margin → MvPolynomial totalDegree = d and computed polyFourierL1 and polyMargin; reason: the finite minimum is positive by strict sign representation; the referenced spectral norm uses the identical cube signs and uniform normalization
--   - encoding: randomized communication after the Newman step → existence of a private-coin protocol with messages in Fin (2^c); reason: private randomness is represented by stochastic encoding and decoding, with c the worst-case bit budget
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, Characterizing Quantum Advantage for Generalizations of the Boolean Hidden Matching Problem, STOC 2027 submission #1085 (October 2026), p. 25, Theorem 12; proof pp. 25–27

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Supplement_Error
import Definitions.Def_BooleanHiddenPartition_LowerBounds_Supplement_PolynomialData

set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds.Supplement

/-- Theorem 12 (pp.25–27). The single absolute constant precedes all problem,
polynomial and error parameters. The inverse degree is used on its defined domain d ≥ 1. -/
theorem classical_upper_bound :
    ∃ A : ℝ, 0 < A ∧
      ∀ (α : ℝ) (d k n m : ℕ) (L : Layout k n m α)
        (f : Cube k → Bool) (p : MvPolynomial (Fin k) ℝ),
        1 ≤ d → d ≤ k → signDegree f = (d : WithTop ℕ) →
        SignRepresents f p → p.totalDegree = d →
        (∀ z : Cube k, |polyOnCube p z| ≤ 1) →
        ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        ∃ (c : ℕ) (P : PrivateCoinProtocol (Cube n) (BobInput n m) c),
          ClassicalSolvesWithError L f P ε ∧
          (c : ℝ) ≤ A *
            ((((k : ℝ) * polyFourierL1 p ^ 2 / (α * polyMargin p ^ 2)) ^
                (1 / (d : ℝ))) *
              (n : ℝ) ^ (1 - 1 / (d : ℝ)) * Real.log (1 / ε) + Real.log (n : ℝ)) := by sorry

end BooleanHiddenPartition.LowerBounds.Supplement
