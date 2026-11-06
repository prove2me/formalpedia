-- Prove2me | Theorems.Thm_ConeL2G_fact_1_3
-- name    : ConeL2G.fact_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:52.823447+00:00
-- url     : https://prove2.me/theorems/d466d6dc-de48-4b87-8074-1e8e00293cec
-- title:
--   Fact 1.3 (corrected: irreducible) — $\langle Df,Df\rangle_\mu\ge\varepsilon\langle Df,f\rangle_\mu$ for all $f$ gives spectral gap $\ge\varepsilon/n$
-- statement:
--   Let $G$ be a finite graph on $n$ vertices with color lists, $\mu$ uniform on its proper list colorings and $D=\sum_iD_i$. Assume that the Glauber dynamics is irreducible on the proper list colorings. If for every function $f$
--   $$\langle Df,Df\rangle_\mu\ \ge\ \varepsilon\,\langle Df,f\rangle_\mu=\varepsilon\sum_i\langle D_if,f\rangle_\mu,\tag{1}$$
--   then the spectral gap of the Glauber dynamics $\frac1nP$ is at least $\varepsilon/n$: for every $f$ with $\mathbb E_\mu f=0$,
--   $$\frac{\varepsilon}{n}\langle f,f\rangle_\mu\le\big\langle f,\tfrac1nDf\big\rangle_\mu .$$
--
--   This turns the operator inequality of Theorem 1.7 into a spectral gap.
--
--   Differences from the source:
--   - correction: no irreducibility assumption → SpinGirth5.GlauberIrreducible (unifMass G L); reason: false for a reducible chain: one edge with L₁ = L₂ = {a, b} has Ω = {(a,b), (b,a)} and D = 0, so (1) holds for every ε, but the gap is 0; the chain is irreducible in the paper's application (|L_i| ≥ deg(i) + 2)
--   - encoding: spectral gap of (1/n)P at least ε/n → SpinGirth5.PoincareIneq µ (glauberLap G L) (ε / n); reason: for a reversible chain the spectral gap is the best constant of the Poincaré inequality for centered f (variational characterization)
--   - encoding: f : Ω → ℝ → f on all assignments V → Fin K with µ-weighted forms; reason: values off Ω never enter; same instances
--   - generalization: G of maximum degree ∆ > 1 (standing assumption, p.1) → any finite graph G; reason: ∆ plays no role in Fact 1.3; the statement specializes to every G with ∆ > 1
--   - encoding: (1) with its trailing identity = ε · Σ_i ⟨D_i f, f⟩_µ → ε * ⟨Df, f⟩_µ ≤ ⟨Df, Df⟩_µ; reason: ⟨Df, f⟩ = Σ_i ⟨D_i f, f⟩ by linearity, as D = Σ_i D_i; the identity adds nothing to the hypothesis
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Fact 1.3, p.2

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_glauberLap

open Finset

namespace ConeL2G

/-- **Fact 1.3 (spectral gap from `D² ⪰ εD`), corrected: irreducible Glauber dynamics.**
Li–Oveis Gharan, arXiv:2610.37721, Fact 1.3, p.2: "If for any function `f : Ω → ℝ`,
`⟨Df, Df⟩_µ ⩾ ε · ⟨Df, f⟩_µ = ε · Σᵢ ⟨Dᵢf, f⟩_µ,` (1)
then the spectral gap of the Glauber dynamics `(1/n)P` is at least `ε/n`."

`G` is a finite graph with lists `L`, `µ = unifMass G L`, `D = SpinGirth5.lapSum µ univ`, `n = |V|`.
"Spectral gap of `(1/n)P` at least `ε/n`" is the Poincaré inequality for the Laplacian
`(1/n)D = glauberLap G L` with constant `ε/n`.

**Correction.** As printed the fact is false when the chain is reducible: one edge with
`L₁ = L₂ = {a, b}` has `Ω = {(a,b), (b,a)}`, `D = 0`, so (1) holds for every `ε`, but the gap is `0`.
The hypothesis that the Glauber dynamics is irreducible on `Ω` (`SpinGirth5.GlauberIrreducible µ`)
is added; it holds in the paper's application (`|Lᵢ| ⩾ deg(i) + 2`).

**Formalization Note.** (1) is written `ε⟨Df, f⟩_µ ⩽ ⟨Df, Df⟩_µ`; the identity
`⟨Df, f⟩ = Σᵢ ⟨Dᵢf, f⟩` is the definition of `D`. -/
theorem fact_1_3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {K : ℕ} (L : V → Finset (Fin K)) (ε : ℝ)
    (hirr : SpinGirth5.GlauberIrreducible (unifMass G L))
    (h1 : ∀ f : (V → Fin K) → ℝ,
      ε * MarkovMixing.innerPi (unifMass G L) (SpinGirth5.lapSum (unifMass G L) univ f) f ≤
        MarkovMixing.innerPi (unifMass G L) (SpinGirth5.lapSum (unifMass G L) univ f)
          (SpinGirth5.lapSum (unifMass G L) univ f)) :
    SpinGirth5.PoincareIneq (unifMass G L) (glauberLap G L) (ε / (Fintype.card V : ℝ)) := by sorry

end ConeL2G
