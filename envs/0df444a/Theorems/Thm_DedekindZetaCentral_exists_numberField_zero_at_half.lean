-- Prove2me | Theorems.Thm_DedekindZetaCentral_exists_numberField_zero_at_half
-- name    : DedekindZetaCentral.exists_numberField_zero_at_half
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T18:49:00.379207+00:00
-- url     : https://prove2.me/theorems/42a9d5e8-6357-4e26-9253-cb477b627d46
-- title:
--   Armitage: there is a number field $K$ whose Dedekind zeta function vanishes at $s=\tfrac12$, with multiplicity at least $2$
-- statement:
--   **A Dedekind zeta function with a zero at the centre of the critical strip (Armitage).** For a number field $K$, the Dedekind zeta function is
--   $$\zeta_K(s)=\sum_{\mathfrak a}\mathrm N\mathfrak a^{-s}\qquad(\operatorname{Re}s>1),$$
--   where the sum runs over the nonzero ideals $\mathfrak a$ of the ring of integers $\mathcal O_K$. It continues to a meromorphic function on $\mathbb C$ whose only pole is a simple pole at $s=1$. The statement is that there exists a number field $K$ such that
--   $$\zeta_K\big(\tfrac12\big)=0\qquad\text{and}\qquad\zeta_K'\big(\tfrac12\big)=0,$$
--   that is, $\zeta_K$ vanishes at the central point $s=\tfrac12$ with multiplicity at least $2$. By contrast, $\zeta_{\mathbb Q}(\tfrac12)=\zeta(\tfrac12)\approx-1.4604\neq0$. A central zero of $\zeta_K$ always has even order, because the completed zeta function is symmetric under $s\mapsto1-s$.
--
--   In the source (p. 529) this classical example (Armitage 1972) illustrates that the central zero of a Dedekind zeta function can have multiplicity larger than $1$. The source cites it in §14.1.2 in its discussion of central zeros, which are excluded from the multiplicity bound $N(\varrho)\le[F:\mathbb Q]$ that the source asserts, in its own Theorem 13.3.1.2, for the other non-trivial zeros $\varrho$ of the Hecke $L$-functions of a number field $F$. That bound is a claim of the source, not an established result; Proposition 14.1.2.3 of the source derives it conditionally on GRH, the Grand Simplicity Hypothesis and Global Langlands. The zero comes from an Artin $L$-function with root number $-1$ in the Artin–Takagi factorization of $\zeta_K$. Note that $\zeta_K$ is the Hecke $L$-function of the trivial character of $K$ and, over $\mathbb Q$, the Artin $L$-function of the permutation representation $\mathrm{Ind}_{\mathrm{Gal}(\overline{\mathbb Q}/K)}^{\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)}\mathbf 1$, which is reducible when $K\neq\mathbb Q$. The example is therefore consistent with Serre's conjecture, recalled on p. 530, that Artin $L$-functions of irreducible representations of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ have only simple zeros.
--
--   **Formalization Note.** Mathlib's `NumberField.dedekindZeta K s` is the Dirichlet series $\sum_n \#\{\mathfrak a:\mathrm N\mathfrak a=n\}\,n^{-s}$, a junk value outside the half-plane of convergence. The statement therefore quantifies over a function $f$ holomorphic on $\mathbb C\setminus\{1\}$ that agrees with it on $\operatorname{Re}s>1$. Since $\mathbb C\setminus\{1\}$ is connected, such an $f$ is unique (identity theorem): it is the meromorphic continuation of $\zeta_K$ restricted to $\mathbb C\setminus\{1\}$. Multiplicity at least $2$ is encoded as $f(\tfrac12)=f'(\tfrac12)=0$. The number field $K$ is sought in `Type` (universe $0$), where every number field has a model.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 529, §14.1.2, discussion following Conjecture 14.1.2.1 (an example of a number field whose Dedekind zeta function vanishes at $s=1/2$ with multiplicity higher than $1$); classical reference: J. V. Armitage, Zeta functions with a zero at $s=1/2$, Inventiones Mathematicae 15 (1972), pp. 199–205 (as cited by the paper at that spot)

import Mathlib

set_option autoImplicit false

namespace DedekindZetaCentral

/-- There is a number field `K` such that the holomorphic continuation `f` of its Dedekind zeta
function to `ℂ \ {1}` vanishes at `s = 1/2` together with its derivative. -/
theorem exists_numberField_zero_at_half :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (f : ℂ → ℂ),
      DifferentiableOn ℂ f {1}ᶜ ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      f (1 / 2) = 0 ∧ deriv f (1 / 2) = 0 := by
  sorry

end DedekindZetaCentral
