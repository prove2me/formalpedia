-- Prove2me | Theorems.Thm_AutomorphicForm_HeckeEigensystem_agreesAwayFromFinite_or_twist_of_formalBaseChange_agreesAwayFromFinite_of_finrank_eq_two_of_coversModCentre
-- name    : AutomorphicForm.HeckeEigensystem.agreesAwayFromFinite_or_twist_of_formalBaseChange_agreesAwayFromFinite_of_finrank_eq_two_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/dd5c68a7-c76d-5a56-a764-834b2f13add5
-- title:
--   Fibre of quadratic base change at Siegel windows
-- statement:
--   Let $L/K$ be an extension of number fields with $\operatorname{finrank}_K L = 2$, and let $\omega$ be a complex-valued function on the height-one primes of $\mathcal O_K$ for which there is a finite set $S$ of primes such that, for every $\mathfrak p \notin S$, $\omega(\mathfrak p)^2 = 1$ and $\omega(\mathfrak p) = 1$ holds precisely when some prime $\mathfrak P$ of $\mathcal O_L$ satisfies $\mathfrak P \cap \mathcal O_K = \mathfrak p$ and $\operatorname{inertiaDeg}'(\mathfrak p, \mathfrak P) = 1$. Over $K$ fix reals $c_K, u_K, d_{1K}, d_{2K}$ and a finite set $T_K \subseteq \mathrm{GL}_2(\mathbb A_K)$, and over $L$ the analogous data; write $W_K = \bigcup_{x \in T_K} (\cdot\, x)(\,\text{centreCutSiegelSet}\,)$ for the union of right translates of the set of adelic matrices whose finite part is finite-integral and whose archimedean part has, at every infinite place, local height at least $c_K$, window square at most $u_K^2$ and determinant norm in $[d_{1K}, d_{2K}]$, and similarly $W_L$. Assume $d_{1K} < d_{2K}$, $d_{1L} < d_{2L}$, and that each of $W_K$, $W_L$ meets the orbit of every adelic point under left multiplication by global $\mathrm{GL}_2$-points and right multiplication by central adelic scalars. Let $\Phi_c, \Phi_c'$ be Hecke eigensystems over $K$ with complex coefficients and $\Phi_L$ one over $L$, each assumed `IsArithGenuineCuspRealizable` for the carrier pins built from the respective window $W$, the adelic Haar measure and Borel structure, full central subgroup, the level groups $N \mapsto \mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$, the Hecke generators $v \mapsto \mathrm{heckeGen}(v)$, and the conditioned additive measure on the adelic box. Assume finally that the formal base changes of $\Phi_c$ and of $\Phi_c'$ to $L$ — the eigensystem of full level with $a_{\mathfrak P} = \mathrm{satakePow}$ of the inertia degree applied to $(a_{\mathfrak p}, b_{\mathfrak p})$ and $b_{\mathfrak P} = b_{\mathfrak p}^{f}$, $\mathfrak p = \mathfrak P \cap \mathcal O_K$ — each agree with $\Phi_L$ at all but finitely many primes. The conclusion: either $\Phi_c'$ and $\Phi_c$ have the same $a$- and $b$-values outside a finite set of primes, or $\Phi_c'$ agrees outside a finite set with the twist of $\Phi_c$ by $\omega$, namely the eigensystem of the same level with values $\omega(v)\,a_v$ and $\omega(v)^2\,b_v$.
--
--   This is the multiplicity statement for the fibre of quadratic base change for $\mathrm{GL}_2$ in the formal Hecke-eigensystem formulation used in this development: two cusp-realizable eigensystems over $K$ with the same base change to the quadratic extension $L$ differ at most by the twist by the quadratic character of $L/K$. It is applied in the Langlands–Tunnell part of the argument, where base-change agreement of weight-one data is converted into agreement up to quadratic twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_HeckeEigensystem_agreesAwayFromFinite_or_twist_of_formalBaseChange_agreesAwayFromFinite_of_finrank_eq_two_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.HeckeEigensystem.agreesAwayFromFinite_or_twist_of_formalBaseChange_agreesAwayFromFinite_of_finrank_eq_two_of_coversModCentre
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hquad : Module.finrank K L = 2)
    (ω : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℂ)
    (hω : ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      ∀ 𝔭 ∉ S, ω 𝔭 ^ 2 = 1 ∧ (ω 𝔭 = 1 ↔
        ∃ 𝔓 : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
          𝔓.under (𝓞 K) = 𝔭 ∧ 𝔭.asIdeal.inertiaDeg' 𝔓.asIdeal = 1))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (hdL : d₁L < d₂L)
    (hcovL : CoversModCentre L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L))
    (Φc Φc' : HeckeEigensystem K ℂ) (ΦL : HeckeEigensystem L ℂ)
    (hΦc : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Φc)
    (hΦc' : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Φc')
    (hΦL : IsArithGenuineCuspRealizable L
      (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)) ΦL)
    (hBC : HeckeEigensystem.AgreesAwayFromFinite (formalBaseChange K L Φc) ΦL)
    (hBC' : HeckeEigensystem.AgreesAwayFromFinite (formalBaseChange K L Φc') ΦL) :
    HeckeEigensystem.AgreesAwayFromFinite Φc' Φc ∨
      HeckeEigensystem.AgreesAwayFromFinite Φc' (Φc.twist ω) := by sorry
