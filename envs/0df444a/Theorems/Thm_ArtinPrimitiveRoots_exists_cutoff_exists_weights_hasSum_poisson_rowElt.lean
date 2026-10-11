-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_weights_hasSum_poisson_rowElt
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_weights_hasSum_poisson_rowElt
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T21:08:51.159641+00:00
-- url     : https://prove2.me/theorems/ea0a8d0e-b8cf-4c20-80da-966e2433ff71
-- title:
--   Lemma 3.1 and p. 45 of OpenAI's Primitive roots paper — Poisson summation on the S-integers, unfolded over U_S⁶, for the weights of (7.1)
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`). There are a smooth real $V$ with compact support in $(0,\infty)$ (`IsProbeWeight V`) and a function $M : \mathbb C \to \mathbb C$, holomorphic on $\operatorname{Re} z > 0$ with rapid vertical decay on its strips (`IsMellinWeight M`) and $M(1/6) \ne 0$, such that for every system of allowed generators $g$ (`AllowedGen ι 𝔪`), every exterior ideal $\mathfrak n$ (`IsExterior 𝔪 𝔫`) with a generator $\nu$ of $\mathfrak n R$, where $R$ is the ring of $S$-integers (`SInt 𝔪`), every $c : R \to \mathbb C$ that is periodic modulo $\mathfrak n R$ and satisfies $c(\varepsilon^6 x) = c(x)$ for every unit $\varepsilon$ of $R$, and every real $T > 0$,
--   $$\sum_{r} c(m_r)\,V\!\left(\frac{q_r}{T}\right) = \frac{T}{q_{\mathfrak n}} \sum_{(u, \mathfrak r)} \hat c(u r^6)\, V_0\!\left(\frac{T q_u q_{\mathfrak r}^6}{q_{\mathfrak n}}\right),\qquad \hat c(h) = \sum_{x \bmod \mathfrak n R} c(x)\, e\!\left(\frac{h x}{\nu}\right),$$
--   as a `HasSum`. Here $r$ runs over the row classes (`RowClass 𝔪`, the nonzero elements of $R$ modulo $U_S^6$), $m_r$ = `rowElt g r`, and $q_r$ is the norm of its ideal; $(u, \mathfrak r)$ runs over the frequency classes (`FreqClass 𝔪`) times the exterior ideals, $u r^6$ = `freqElt g u * g.gen 𝔯 ^ 6`, $q_u$ and $q_{\mathfrak r}$ are norms, and $q_{\mathfrak n} = N\mathfrak n$. The residue classes are lifted by `quotLift`, $e$ is `sAddChar 𝔪`, and $V_0$ = `mellinInv 2 M` (bundle `Def_ArtinHeckeTheta`).
--
--   In the paper, $V$ and $V_0$ are the norm-sheet profiles $T \mapsto \int_{F_S^1} W_0(t\ell_T)\,dt$ and $\int_{F_S^1}\widehat W_0(t\ell_T)\,dt$ of the weight $W_0$ of (7.1), and $M$ is the Mellin transform of $V_0$. The identity is Lemma 3.1 for $f = W_0(\,\cdot\,/t_0\ell_T)$ on the lattice $\nu R$, of index $q_{\mathfrak n}$ in $R$, integrated over $F_S^1/U_S^6$ and unfolded on both sides as on p. 45. The term $m = 0$ vanishes because $W_0$ is supported in $F_S^\times$, the term $h = 0$ because $\widehat W_0(0) = 0$, and the nonzero $h$ modulo $U_S^6$ are written uniquely as $u r^6$ by (3.7). With $\mathfrak n = \mathfrak s\mathfrak A$, $\nu = sA$, $c(x) = g_{\mathfrak s}(-x)\chi_{\mathfrak A}(x)$ and $T = q_{\mathfrak s}X$ it gives, by (7.8), the Poisson expression (7.9), and with it a cut for `exists_cutoff_exists_weights_hasSum_rowIntegral`.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 9, Lemma 3.1: “The diagonal copy of $R$ is a discrete cocompact subgroup of $F_S$, is its own annihilator for the pairing $e(xy)$, and has covolume 1. For every Bruhat–Schwartz function $f$ on $F_S$, $\sum_{m \in R} f(m) = \sum_{\nu \in R}\widehat f(\nu)$.”; p. 45: “Sum the nonzero $h$’s in such orbits and unfold the quotient $F_S^1/U_S^6$. If $V_0(T) = \int_{F_S^1}\widehat W_0(t\ell_T)\,dt$, the orbit of $h$ contributes $F(s, A, h)V_0(Xq_h/q_A)$. […] The zero frequency contributes nothing because $\widehat W_0(0) = 0$. By the measure disintegration, the Mellin transform of $V_0$ is $M$.” For Lemma 3.1 the paper cites A. Weil, *Sur certains groupes d’opérateurs unitaires*, Acta Math. 111 (1964), 143–211, Chapter II, §29, https://doi.org/10.1007/BF02391012.
-- source:
--   A. Weil, Sur certains groupes d'opérateurs unitaires, Acta Math. 111 (1964), 143–211, https://doi.org/10.1007/BF02391012, p. 143–211, Chapter II, §29 (the self-dual lattice of S-integers and Poisson summation; cited for Lemma 3.1 of OpenAI, Primitive roots for every admissible integer base, p. 9, here with the unfolding over U_S⁶ of p. 45 and the weights of (7.1), p. 42)

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_exists_weights_hasSum_poisson_rowElt (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∃ (V : ℝ → ℝ) (M : ℂ → ℂ), IsProbeWeight V ∧ IsMellinWeight M ∧ M (1 / 6) ≠ 0 ∧
        ∀ (g : AllowedGen ι 𝔪) (𝔫 : Ideal (𝓞 F)), IsExterior 𝔪 𝔫 →
          ∀ ν : SInt 𝔪, Ideal.span {ν} = 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) →
          ∀ c : SInt 𝔪 → ℂ,
            (∀ x y : SInt 𝔪, y ∈ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)) → c (x + y) = c x) →
            (∀ (x : SInt 𝔪) (ε : (SInt 𝔪)ˣ), c ((ε : SInt 𝔪) ^ 6 * x) = c x) →
            ∀ T : ℝ, 0 < T →
              HasSum (fun r : RowClass 𝔪 =>
                  c (rowElt g r) * ((V (Ideal.absNorm r.1.1 / T) : ℝ) : ℂ))
                (((T / Ideal.absNorm 𝔫 : ℝ) : ℂ) *
                  ∑' p : FreqClass 𝔪 × {𝔯 : Ideal (𝓞 F) // IsExterior 𝔪 𝔯},
                    (∑ᶠ x : SInt 𝔪 ⧸ 𝔫.map (algebraMap (𝓞 F) (SInt 𝔪)),
                      c (quotLift x) * sAddChar 𝔪
                        (((freqElt g p.1 * g.gen p.2.1 ^ 6 : SInt 𝔪) : F) * (quotLift x : F) /
                          (ν : F))) *
                    mellinInv 2 M (T * (Ideal.absNorm p.1.1.1 * Ideal.absNorm p.2.1 ^ 6) /
                      Ideal.absNorm 𝔫)) := by
  sorry

end ArtinPrimitiveRoots
